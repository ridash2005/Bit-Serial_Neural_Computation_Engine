`timescale 1ns/1ps

module bitserial_nn #(
    parameter int DATA_W    = 16,
    parameter int PRECISION = DATA_W,
    parameter int N_IN      = 128,
    parameter int N_HIDDEN  = 64,
    parameter int N_LAYERS = 3,
    parameter int P         = 4
)(
    input  logic clk,
    input  logic rst_n,

     
    // AXI-Stream INPUT (features)
     
    input  logic signed [DATA_W-1:0] s_axis_tdata,
    input  logic                     s_axis_tvalid,
    output logic                     s_axis_tready,
    input  logic                     s_axis_tlast,

     
    // Weight memory write
     
    input  logic w_wr_en,
    input  logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h,
    input  logic [$clog2((N_IN>1)?N_IN:2)-1:0]         w_addr_i,
    input  logic [$clog2((N_LAYERS>1)?N_LAYERS:2)-1:0] w_addr_l,
    input  logic signed [DATA_W-1:0]                  w_data,

     
    // AXI-Stream OUTPUT (hidden activations)
     
    output logic signed [(2*DATA_W)+$clog2((N_IN>1)?N_IN:2)-1:0] m_axis_tdata,
    output logic                                               m_axis_tvalid,
    input  logic                                               m_axis_tready,
    output logic                                               m_axis_tlast,

    // Global busy
    output logic                                               busy
);

     
    // Local parameters
     
    localparam int ACC_W = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);
    localparam int IN_VEC_W = N_IN * DATA_W;
    localparam int WMEM_ADDR_W = $clog2(((N_HIDDEN*N_IN)>1)?(N_HIDDEN*N_IN):2);

     
    // Internal signals
     
    logic signed [IN_VEC_W-1:0] invec_bus;
    logic                      vector_done;

    logic [WMEM_ADDR_W-1:0]    wmem_raddr;
    logic signed [DATA_W-1:0]  wmem_rdata;

    logic [$clog2(N_LAYERS)-1:0] cur_layer;
    logic                        layer_done;

    logic signed [ACC_W-1:0]   mac_out_data;
    logic                      mac_out_valid;
    logic                      mac_out_ready;

    logic signed [ACC_W-1:0]   relu_out_data;
    logic                      relu_out_valid;
    logic                      relu_out_ready;
    logic                      relu_in_ready;

    integer i, l, h;

     
    // AXI INPUT HANDSHAKE
     
    assign s_axis_tready = ~busy;

     
    // Input buffer
     
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

    logic signed [N_IN*ACC_W-1:0] layer_invec;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            layer_invec <= '0;
        end else begin
             for (i = 0; i < N_IN; i++) begin
                if (cur_layer == 0)
                    // sign-extend input data to ACC_W
                    layer_invec[(i+1)*ACC_W-1 -: ACC_W]
                        <= {{(ACC_W-DATA_W){invec_bus[(i+1)*DATA_W-1]}},
                        invec_bus[(i+1)*DATA_W-1 -: DATA_W]};
                else if (i < N_HIDDEN)
                    // Use full-precision stored activation
                    layer_invec[(i+1)*ACC_W-1 -: ACC_W]
                    <= act_mem[cur_layer-1][i];
                else
                    layer_invec[(i+1)*ACC_W-1 -: ACC_W] <= '0;
            end
        end
    end



    // Hidden-layer weight memory
     
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

     
    // MAC Engine (AXI backpressure)

    logic start_compute_req;
    logic mac_accept;
    logic layer_invec_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            layer_invec_valid <= 1'b0;
        // Set when input or previous layer completes
        else if ((cur_layer == 0 && vector_done) ||
            (cur_layer != 0 && layer_done))
            layer_invec_valid <= 1'b1;

    // Clear only when MAC accepts
    else if (mac_accept)
        layer_invec_valid <= 1'b0;
    end

    assign mac_accept = start_compute_req && !busy && layer_invec_valid;

    /* ---------------- START COMPUTE REQUEST ---------------- */
    always_ff @(posedge clk) begin
        if (!rst_n)
            start_compute_req <= 1'b0;

        // Raise request
        else if ((cur_layer == 0 && vector_done) ||
                (cur_layer != 0 && layer_done))
            start_compute_req <= 1'b1;

        // Clear ONLY when MAC accepts it
        else if (mac_accept)
            start_compute_req <= 1'b0;
    end

    // Layer counter

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

    assign mac_out_ready = relu_in_ready;

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
        .start_compute (start_compute_req),
        .invec_bus     (layer_invec),
        .wmem_raddr    (wmem_raddr),
        .wmem_rdata    (wmem_rdata),
        .out_data      (mac_out_data),
        .out_valid     (mac_out_valid),
        .out_ready     (mac_out_ready),
        .layer_done    (layer_done),
        .busy          (busy)
    );

     
    // ReLU (AXI-compliant)
     
    assign relu_out_ready = (cur_layer == N_LAYERS-1) ? m_axis_tready : 1'b1;

    relu_activation #(
        .ACC_W (ACC_W)
    ) u_relu_activation (
        .clk       (clk),
        .rst_n     (rst_n),
        .in_data   (mac_out_data),
        .in_valid  (mac_out_valid),
        .out_ready (relu_out_ready),
        .out_data  (relu_out_data),
        .out_valid (relu_out_valid),
        .in_ready  (relu_in_ready)
    );

    // Store activations into activation memory

    logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] act_idx;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset activation memory
            for (l = 0; l < N_LAYERS; l++)
                for (h = 0; h < N_HIDDEN; h++)
                    act_mem[l][h] <= '0;

            act_idx <= '0;
        end

        else begin
        /* ---------------- RESET INDEX AT LAYER BOUNDARY ---------------- */
        if (layer_done) begin
            act_idx <= '0;
        end

        /* ---------------- STORE ACTIVATION ---------------- */
        else if (relu_out_valid && relu_in_ready && cur_layer < N_LAYERS-1) begin
            act_mem[cur_layer][act_idx] <= relu_out_data;

            if (act_idx < N_HIDDEN-1)
                act_idx <= act_idx + 1'b1;
        end

        
    end
    end

     
    // AXI OUTPUT HANDSHAKE
     
    logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] out_idx;

    /* ---------------- OUTPUT INDEX ---------------- */
    always_ff @(posedge clk) begin
        if (!rst_n)
            out_idx <= '0;

        // reset index when starting final layer
        else if (layer_done && cur_layer == N_LAYERS-2)
            out_idx <= '0;

        // increment only on successful transfer
        else if (m_axis_tvalid && m_axis_tready)
            out_idx <= out_idx + 1'b1;
    end

    /* ---------------- AXI OUTPUT ---------------- */
    assign m_axis_tdata =
        (cur_layer == N_LAYERS-1) ? relu_out_data : '0;

    assign m_axis_tvalid =
        (cur_layer == N_LAYERS-1) && relu_out_valid;

    /* ---------------- TLAST (FIXED) ---------------- */
    assign m_axis_tlast =
        (cur_layer == N_LAYERS-1) &&
        (out_idx == N_HIDDEN-1) &&
        m_axis_tvalid &&
        m_axis_tready;

`ifndef SYNTHESIS
    always_ff @(posedge clk) begin
        if (w_wr_en && busy)
            $warning("Writing weights while MAC is busy");
    end
`endif

endmodule