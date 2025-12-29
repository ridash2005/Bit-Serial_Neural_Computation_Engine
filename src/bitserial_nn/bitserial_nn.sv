`timescale 1ns/1ps

module bitserial_nn #(
    parameter int DATA_W    = 16,
    parameter int PRECISION = DATA_W,
    parameter int N_IN      = 128,
    parameter int N_HIDDEN  = 64,
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

    logic signed [ACC_W-1:0]   mac_out_data;
    logic                      mac_out_valid;
    logic                      mac_out_ready;

    logic signed [ACC_W-1:0]   relu_out_data;
    logic                      relu_out_valid;
    logic                      relu_out_ready;
    logic                      relu_in_ready;

     
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

     
    // Hidden-layer weight memory
     
    wmem_hidden #(
        .DATA_W   (DATA_W),
        .N_IN     (N_IN),
        .N_HIDDEN (N_HIDDEN)
    ) u_wmem_hidden (
        .clk      (clk),
        .rst_n    (rst_n),
        .w_wr_en  (w_wr_en),
        .w_addr_h (w_addr_h),
        .w_addr_i (w_addr_i),
        .w_data   (w_data),
        .raddr    (wmem_raddr),
        .rdata    (wmem_rdata)
    );

     
    // MAC Engine (AXI backpressure)
     
    assign mac_out_ready = relu_in_ready;

    mac_engine #(
        .DATA_W    (DATA_W),
        .PRECISION (PRECISION),
        .N_IN      (N_IN),
        .N_HIDDEN  (N_HIDDEN),
        .P         (P)
    ) u_mac_engine (
        .clk           (clk),
        .rst_n         (rst_n),
        .start_compute (vector_done),
        .invec_bus     (invec_bus),
        .wmem_raddr    (wmem_raddr),
        .wmem_rdata    (wmem_rdata),
        .out_data      (mac_out_data),
        .out_valid     (mac_out_valid),
        .out_ready     (mac_out_ready),
        .busy          (busy)
    );

     
    // ReLU (AXI-compliant)
     
    assign relu_out_ready = m_axis_tready;

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

     
    // AXI OUTPUT HANDSHAKE
     
    logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] out_idx;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            out_idx <= '0;
        end else if (relu_out_valid && m_axis_tready) begin
            out_idx <= (out_idx == N_HIDDEN-1) ? '0 : out_idx + 1'b1;
        end
    end

    assign m_axis_tdata  = relu_out_data;
    assign m_axis_tvalid = relu_out_valid;
    assign m_axis_tlast  = (out_idx == N_HIDDEN-1) && m_axis_tvalid;

`ifndef SYNTHESIS
    always_ff @(posedge clk) begin
        if (w_wr_en && busy)
            $warning("Writing weights while MAC is busy");
    end
`endif

endmodule