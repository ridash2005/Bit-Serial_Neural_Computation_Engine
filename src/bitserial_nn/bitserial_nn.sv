`timescale 1ns/1ps

/**
 * Module: bitserial_nn
 * Description: Top-Level Bit-Serial Neural Computation Engine.
 *              Integrates input buffering, weight memory, MAC engine, 
 *              and ReLU activation. Supports multi-layer inference 
 *              via internal activation recycling.
 */

/* Xilinx IP Decorators for automated packaging */
(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clk CLK" *)
(* X_INTERFACE_PARAMETER = "ASSOCIATED_BUSIF s_axis:m_axis, ASSOCIATED_RESET rst_n" *)
module bitserial_nn #(
    parameter int DATA_W    = 16,  // bit-width of input features and weights
    parameter int PRECISION = 16,  // bit-serial processing cycles
    parameter int N_IN      = 4,   // input vector size
    parameter int N_HIDDEN  = 8,   // hidden layer size
    parameter int N_LAYERS  = 2,   // total number of layers to compute
    parameter int P         = 1    // internal parallelism (processing lanes)
)(
    input  logic clk,   // master clock
    
    (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 rst_n RST" *)
    (* X_INTERFACE_PARAMETER = "POLARITY ACTIVE_LOW" *)
    input  logic rst_n, // asynchronous active-low reset

    /**
     * Weight Loader Interface:
     * Used to populate internal BRAM with weights before starting inference.
     */
    input  logic                                        w_wr_en,
    input  logic [$clog2((N_LAYERS > 1) ? N_LAYERS : 2)-1:0]  w_addr_l,
    input  logic [$clog2((N_HIDDEN > 1) ? N_HIDDEN : 2)-1:0]  w_addr_h,
    input  logic [$clog2((N_IN > 1) ? N_IN : 2)-1:0]          w_addr_i,
    input  logic signed [DATA_W-1:0]                   w_data,

    /**
     * Slave AXI-Stream (Input Vector):
     * Receives the external input features for Layer 0.
     */
    input  logic [DATA_W-1:0] s_axis_tdata,
    input  logic              s_axis_tvalid,
    output logic              s_axis_tready,
    input  logic              s_axis_tlast, // marks end of input vector

    /**
     * Master AXI-Stream (Output Activations):
     * Streams out the final layer's computed activations.
     */
    output logic [DATA_W-1:0] m_axis_tdata,
    output logic              m_axis_tvalid,
    input  logic              m_axis_tready,
    output logic              m_axis_tlast  // marks end of output vector
);

    // Dynamic width calculation for internal accumulators
    localparam int ACC_W = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);
    localparam int WMEM_SIZE = N_LAYERS * N_HIDDEN * N_IN;
    localparam int WMEM_ADDR_W = $clog2((WMEM_SIZE>1)?WMEM_SIZE:2);

    // --- 1. SIGNAL DECLARATIONS ---

    // Controller State
    logic [$clog2(N_LAYERS)-1:0] cur_layer; // current processing depth
    logic busy;                             // status indicator

    // Input Buffer Signals
    logic [N_IN*DATA_W-1:0] in_bus;    // parallelized input vector
    logic                   vector_done; // complete vector received pulse

    // Weight Memory Signals
    logic [WMEM_ADDR_W-1:0]     w_raddr;
    logic signed [DATA_W-1:0]  w_rdata;

    // MAC Engine Signals
    logic                      start_compute_req; // trigger MAC math
    logic                      mac_accept;        // MAC acknowledged start
    logic                      mac_busy;
    logic                      layer_done;        // entire layer completed pulse
    
    // Activation Memory (Internal BRAM for intermediate layers)
    logic signed [DATA_W-1:0]  act_mem [0:N_HIDDEN-1];
    logic [$clog2(N_HIDDEN)-1:0] act_idx; // write pointer

    // ReLU Pipeline Signals
    logic [ACC_W-1:0]          relu_in;
    logic                      relu_in_v;
    logic                      relu_in_r;
    logic [ACC_W-1:0]          relu_out;
    logic                      relu_out_v;
    logic                      relu_out_r;

    // Streaming State
    logic [$clog2(N_HIDDEN)-1:0] out_idx; // master stream counter


    // --- 2. INPUT VECTOR PARALLELIZER ---
    /**
     * Buffer external serial data until a full 'N_IN' vector is ready.
     * Stalls if MAC is still busy with a previous request.
     */
    input_buffer #(
        .DATA_W(DATA_W),
        .N_IN(N_IN)
    ) inbuf_inst (
        .clk        (clk),
        .rst_n      (rst_n),
        .data_in    (s_axis_tdata),
        .data_in_valid(s_axis_tvalid),
        .vector_last(s_axis_tlast),
        .ready      (s_axis_tready),
        .busy       (busy), // Stall if engine is busy or streaming
        .buffer_out (in_bus),
        .vector_done(vector_done)
    );


    // --- 3. WEIGHT STORAGE (BRAM) ---
    /**
     * Stores all layer weights in a linear space. 
     * Indexed by L*H*I + h*I + i.
     */
    wmem_hidden #(
        .DATA_W(DATA_W),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .N_LAYERS(N_LAYERS)
    ) wmem_inst (
        .clk        (clk),
        .rst_n      (rst_n),
        .w_wr_en    (w_wr_en),
        .w_addr_l   (w_addr_l),
        .w_addr_h   (w_addr_h),
        .w_addr_i   (w_addr_i),
        .w_data     (w_data),
        .raddr      (w_raddr),
        .rdata      (w_rdata)
    );


    // --- 4. LAYER MULTIPLEXING LOGIC ---
    /**
     * Logic to decide if we use the external input vector (Layer 0)
     * or computed activations from the internal buffer (Layer > 0).
     */
    logic [N_IN*DATA_W-1:0] layer_invec_reg;
    logic                   layer_invec_valid;
    logic                   start_compute_pulse;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            layer_invec_reg   <= '0;
            layer_invec_valid <= 1'b0;
        end else begin
            // Capture external vector for L0
            if (cur_layer == 0 && vector_done) begin
                layer_invec_reg   <= in_bus;
                layer_invec_valid <= 1'b1;
            end 
            // Reuse activations for higher layers
            else if (cur_layer != 0 && layer_done) begin
                for (int i=0; i < N_IN; i++) begin
                    layer_invec_reg[i*DATA_W +: DATA_W] <= (i < N_HIDDEN) ? act_mem[i] : '0;
                end
                layer_invec_valid <= 1'b1;
            end 
            // Clear valid flag once MAC accepts
            else if (mac_accept) begin
                layer_invec_valid <= 1'b0;
            end
        end
    end

    // MAC Compute Trigger Pulse
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
            start_compute_pulse <= 1'b0;
        else if (layer_invec_valid)
            start_compute_pulse <= 1'b1;
        else if (mac_accept)
            start_compute_pulse <= 1'b0;
    end

    // Register trigger for timing alignment
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) start_compute_req <= 1'b0;
        else        start_compute_req <= start_compute_pulse;
    end


    // --- 5. BIT-SERIAL MAC ENGINE ---
    /**
     * Performs vector-matrix multiplication for the current layer.
     */
    mac_engine #(
        .DATA_W(DATA_W),
        .PRECISION(PRECISION),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .N_LAYERS(N_LAYERS),
        .P(P)
    ) mac_inst (
        .clk            (clk),
        .rst_n          (rst_n),
        .layer_idx      (cur_layer),
        .start_compute  (start_compute_req),
        .invec_bus      (layer_invec_reg),
        .wmem_raddr     (w_raddr),
        .wmem_rdata     (w_rdata),
        .out_data       (relu_in),
        .out_valid      (relu_in_v),
        .out_ready      (relu_in_r),
        .busy           (mac_busy),
        .layer_done     (layer_done)
    );


    // --- 6. ReLU ACTIVATION UNIT ---
    /**
     * Nonlinearity module with skid buffering for backpressure support.
     */
    relu_activation #(
        .ACC_W(ACC_W)
    ) relu_inst (
        .clk        (clk),
        .rst_n      (rst_n),
        .in_data    (relu_in),
        .in_valid   (relu_in_v),
        .in_ready   (relu_in_r),
        .out_ready  (relu_out_r),
        .out_data   (relu_out),
        .out_valid  (relu_out_v)
    );


    // --- 7. MAIN CONTROLLER & MEMORY MANAGER ---
    /**
     * Managed layer progression and internal activation storage.
     */
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cur_layer <= '0;
            busy      <= 1'b0;
            act_idx   <= '0;
            out_idx   <= '0;
        end else begin
            // 7a. Input Received -> Start Engine
            if (vector_done && cur_layer == 0) begin
                busy <= 1'b1;
            end

            // 7b. Save Middle Activations to internal RAM
            if (relu_out_v && relu_out_r && cur_layer != N_LAYERS-1) begin
                act_mem[act_idx] <= relu_out[DATA_W-1:0]; // truncate to DATA_W
                act_idx <= act_idx + 1;
            end

            // 7c. Layer Transition logic
            if (layer_done) begin
                act_idx <= '0;
                // Last layer completed?
                if (cur_layer == N_LAYERS-1) begin
                    // Move to streaming
                end else begin
                    cur_layer <= cur_layer + 1;
                end
            end

            // 7d. Master Stream Counter
            if (m_axis_tvalid && m_axis_tready) begin
                if (out_idx == N_HIDDEN-1) begin
                    out_idx   <= '0;
                    cur_layer <= '0;
                    busy      <= 1'b0;
                end else begin
                    out_idx <= out_idx + 1;
                end
            end
        end
    end


    // --- 8. OUTPUT INTERFACE (MASTER AXI-S) ---
    /**
     * Final layer results bypass the internal memory and stream out.
     */
    assign relu_out_r = (cur_layer == N_LAYERS-1) ? m_axis_tready : 1'b1;

    assign m_axis_tdata  = (cur_layer == N_LAYERS-1) ? relu_out[DATA_W-1:0] : '0;
    assign m_axis_tvalid = (cur_layer == N_LAYERS-1) && relu_out_v;

    // tlast signals the end of the final layer's vector
    assign m_axis_tlast = (cur_layer == N_LAYERS-1) && (out_idx == N_HIDDEN-1) && m_axis_tvalid;

    // Pulse signal MAC Engine accepted the request
    assign mac_accept = start_compute_req && mac_busy;

    // Engine is ready for next vector only when IDLE and not busy
    assign s_axis_tready = !busy;

endmodule