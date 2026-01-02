`timescale 1ns/1ps

module bitserial_nn #(
    parameter int DATA_W    = 16,
    parameter int PRECISION = DATA_W,
    parameter int N_IN      = 128,
    parameter int N_HIDDEN  = 64,
    parameter int N_LAYERS  = 3,
    parameter int P         = 4
)(
    input  logic clk,
    input  logic rst_n,

    // AXI-Stream INPUT
    input  logic signed [DATA_W-1:0] s_axis_tdata,
    input  logic                     s_axis_tvalid,
    output logic                     s_axis_tready,
    input  logic                     s_axis_tlast,

    // Weight memory write (layer-aware)
    input  logic w_wr_en,
    input  logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h,
    input  logic [$clog2((N_IN>1)?N_IN:2)-1:0]         w_addr_i,
    input  logic [$clog2(N_LAYERS)-1:0]                w_addr_l,
    input  logic signed [DATA_W-1:0]                   w_data,

    // AXI-Stream OUTPUT (FINAL LAYER ONLY)
    output logic signed [(2*DATA_W)+$clog2((N_IN>1)?N_IN:2)-1:0] m_axis_tdata,
    output logic                                               m_axis_tvalid,
    input  logic                                               m_axis_tready,
    output logic                                               m_axis_tlast,

    // Status
    output logic                                               busy
);

    /* ---------------- LOCAL PARAMETERS ---------------- */

    localparam int ACC_W =
        (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);

    localparam int IN_VEC_W = N_IN * DATA_W;

    localparam int WMEM_ADDR_W =
        $clog2(((N_LAYERS*N_HIDDEN*N_IN)>1)?
                (N_LAYERS*N_HIDDEN*N_IN):2);

    /* ---------------- INTERNAL STATE ---------------- */

    logic [$clog2(N_LAYERS)-1:0] cur_layer;
    logic                        layer_done;

    /* ---------------- INPUT BUFFER ---------------- */

    logic signed [IN_VEC_W-1:0] invec_bus;
    logic                      vector_done;

    assign s_axis_tready = ~busy;

    input_buffer #(
        .DATA_W (DATA_W),
        .N_IN   (N_IN)
    ) u_input_buffer (
        .clk           (clk),
        .rst_n         (rst_n),
        .data_in       (s_axis_tdata),
        .data_in_valid (s_axis_tvalid & s_axis_tready),
        .vector_last   (s_axis_tlast),
        .busy          (busy),
        .invec_bus     (invec_bus),
        .vector_done   (vector_done)
    );

    /* ---------------- ACTIVATION MEMORY ---------------- */

    logic signed [ACC_W-1:0] act_mem [0:N_LAYERS-1][0:N_HIDDEN-1];

    /* ---------------- LAYER INPUT MUX ---------------- */

    logic signed [IN_VEC_W-1:0] layer_invec;

    genvar gi;
    generate
        for (gi = 0; gi < N_IN; gi++) begin : PACK_ACT
            assign layer_invec[(gi+1)*DATA_W-1 -: DATA_W] =
                (cur_layer == 0) ?
                    invec_bus[(gi+1)*DATA_W-1 -: DATA_W] :
                    act_mem[cur_layer-1][gi][DATA_W-1:0];
        end
    endgenerate

    /* ---------------- WEIGHT MEMORY ---------------- */

    logic [WMEM_ADDR_W-1:0]   wmem_raddr;
    logic signed [DATA_W-1:0] wmem_rdata;

    wmem_hidden #(
        .DATA_W   (DATA_W),
        .N_IN     (N_IN),
        .N_HIDDEN (N_HIDDEN),
        .N_LAYERS (N_LAYERS)
    ) u_wmem_hidden (
        .clk      (clk),
        .rst_n    (rst_n),
        .w_wr_en  (w_wr_en),
        .w_addr_l (w_addr_l),
        .w_addr_h (w_addr_h),
        .w_addr_i (w_addr_i),
        .w_data   (w_data),
        .raddr    (wmem_raddr),
        .rdata    (wmem_rdata)
    );

    /* ---------------- MAC ENGINE ---------------- */

    logic signed [ACC_W-1:0] mac_out_data;
    logic                    mac_out_valid;
    logic                    mac_out_ready;

    mac_engine #(
        .DATA_W    (DATA_W),
        .PRECISION (PRECISION),
        .N_IN      (N_IN),
        .N_HIDDEN  (N_HIDDEN),
        .N_LAYERS  (N_LAYERS),
        .P         (P)
    ) u_mac_engine (
        .clk           (clk),
        .rst_n         (rst_n),
        .layer_idx     (cur_layer),
        .start_compute ((cur_layer == 0) ? vector_done : layer_done),
        .invec_bus     (layer_invec),
        .wmem_raddr    (wmem_raddr),
        .wmem_rdata    (wmem_rdata),
        .out_data      (mac_out_data),
        .out_valid     (mac_out_valid),
        .out_ready     (mac_out_ready),
        .layer_done    (layer_done),
        .busy          (busy)
    );

    /* ---------------- ReLU ---------------- */

    logic signed [ACC_W-1:0] relu_out_data;
    logic                    relu_out_valid;
    logic                    relu_in_ready;

    assign mac_out_ready = relu_in_ready;

    relu_activation #(
        .ACC_W (ACC_W)
    ) u_relu (
        .clk       (clk),
        .rst_n     (rst_n),
        .in_data   (mac_out_data),
        .in_valid  (mac_out_valid),
        .out_ready ((cur_layer == N_LAYERS-1) ? m_axis_tready : 1'b1),
        .out_data  (relu_out_data),
        .out_valid (relu_out_valid),
        .in_ready  (relu_in_ready)
    );

    /* ---------------- STORE INTERMEDIATE ACTIVATIONS ---------------- */

    logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] act_idx;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            act_idx <= '0;
        end
        else if (relu_out_valid) begin
            if (cur_layer < N_LAYERS-1) begin
                act_mem[cur_layer][act_idx] <= relu_out_data;
                act_idx <= act_idx + 1'b1;
            end
        end

        if (layer_done)
            act_idx <= '0;
    end

    /* ---------------- LAYER COUNTER ---------------- */

    always_ff @(posedge clk) begin
        if (!rst_n)
            cur_layer <= '0;
        else if (layer_done) begin
            if (cur_layer == N_LAYERS-1)
                cur_layer <= '0;
            else
                cur_layer <= cur_layer + 1'b1;
        end
    end

    /* ---------------- AXI OUTPUT (FINAL LAYER ONLY) ---------------- */

    logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] out_idx;

    always_ff @(posedge clk) begin
        if (!rst_n)
            out_idx <= '0;
        else if (relu_out_valid && m_axis_tready && cur_layer == N_LAYERS-1)
            out_idx <= out_idx + 1'b1;
    end

    assign m_axis_tdata  =
        (cur_layer == N_LAYERS-1) ? relu_out_data : '0;

    assign m_axis_tvalid =
        (cur_layer == N_LAYERS-1) && relu_out_valid;

    assign m_axis_tlast =
        (cur_layer == N_LAYERS-1) &&
        (out_idx == N_HIDDEN-1) &&
        m_axis_tvalid;

`ifndef SYNTHESIS
    always_ff @(posedge clk) begin
        if (w_wr_en && busy)
            $warning("Writing weights while MAC is busy");
    end
`endif

endmodule
