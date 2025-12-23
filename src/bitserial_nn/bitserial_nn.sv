`timescale 1ns/1ps

module bitserial_nn #(
    parameter int DATA_W    = 16,
    parameter int PRECISION = DATA_W,   // bit-serial compute precision
    parameter int N_IN      = 128,
    parameter int N_HIDDEN  = 64,
    //parameter int N_OUT     = 10,        // reserved for future output layer
    parameter int P         = 4
)(
    input  logic clk,
    input  logic rst_n,

    // -------------------------------------------------
    // Streaming input
    // -------------------------------------------------
    input  logic signed [DATA_W-1:0] data_in,
    input  logic                     data_in_valid,

    // Start computation (vector-level)
    input  logic start,

    // -------------------------------------------------
    // Weight memory write (hidden layer only)
    // -------------------------------------------------
    input  logic w_wr_en,
    input  logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h,
    input  logic [$clog2((N_IN>1)?N_IN:2)-1:0]         w_addr_i,
    input  logic signed [DATA_W-1:0]                  w_data,

    // -------------------------------------------------
    // Output stream (hidden activations after ReLU)
    // -------------------------------------------------
    output logic signed [(2*DATA_W)+$clog2((N_IN>1)?N_IN:2)-1:0] out_data,
    output logic                                               out_valid,

    // Global busy (MAC active)
    output logic                                               busy
);

    // ------------------------------------------------------------------
    // Local parameters
    // ------------------------------------------------------------------
    localparam int ACC_W =
        (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);

    localparam int IN_VEC_W =
        N_IN * DATA_W;

    localparam int WMEM_ADDR_W =
        $clog2(((N_HIDDEN*N_IN)>1)?(N_HIDDEN*N_IN):2);

    // ------------------------------------------------------------------
    // Internal signals
    // ------------------------------------------------------------------
    logic signed [IN_VEC_W-1:0] invec_bus;
    logic                      vector_done;

    logic [WMEM_ADDR_W-1:0]    wmem_raddr;
    logic signed [DATA_W-1:0]  wmem_rdata;

    logic signed [ACC_W-1:0]   mac_out_data;
    logic                      mac_out_valid;

    // ------------------------------------------------------------------
    // Input buffer (stalls when MAC is busy)
    // ------------------------------------------------------------------
    input_buffer #(
        .DATA_W (DATA_W),
        .N_IN   (N_IN)
    ) u_input_buffer (
        .clk           (clk),
        .rst_n         (rst_n),
        .data_in       (data_in),
        .data_in_valid (data_in_valid),
        .busy          (busy),        // <-- IMPORTANT FIX
        .invec_bus     (invec_bus),
        .vector_done   (vector_done)
    );

    // ------------------------------------------------------------------
    // Hidden-layer weight memory (1R1W BRAM)
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // Bit-serial MAC engine (hidden layer)
    // ------------------------------------------------------------------
    mac_engine #(
        .DATA_W    (DATA_W),
        .PRECISION (PRECISION),
        .N_IN      (N_IN),
        .N_HIDDEN  (N_HIDDEN),
        .P         (P)
    ) u_mac_engine (
        .clk           (clk),
        .rst_n         (rst_n),
        .start_compute (start & vector_done),
        .invec_bus     (invec_bus),
        .wmem_raddr    (wmem_raddr),
        .wmem_rdata    (wmem_rdata),
        .out_data      (mac_out_data),
        .out_valid     (mac_out_valid),
        .busy          (busy)
    );

    // ------------------------------------------------------------------
    // ReLU activation (hidden outputs)
    // ------------------------------------------------------------------
    relu_activation #(
        .ACC_W (ACC_W)
    ) u_relu_activation (
        .clk       (clk),
        .rst_n     (rst_n),
        .in_data   (mac_out_data),
        .in_valid  (mac_out_valid),
        .out_data  (out_data),
        .out_valid (out_valid)
    );

`ifndef SYNTHESIS
always_ff @(posedge clk)
    if (w_wr_en && busy)
        $warning("Writing weights while MAC is busy");
`endif

endmodule
