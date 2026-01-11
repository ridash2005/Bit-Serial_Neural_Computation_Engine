`timescale 1ns/1ps

/**
 * Module: mac_engine
 * Description: Core Multiply-Accumulate (MAC) engine using bit-serial optimization.
 *              Processes input vectors through multiple hidden layers by interleaving
 *              memory reads and shift-accumulation.
 *              Compliant with AXI-Stream for output activations.
 */
module mac_engine #(
    parameter int unsigned DATA_W    = 16, // Width of input data/weights
    parameter int unsigned PRECISION = DATA_W, // Accuracy (number of cycles per mult)
    parameter int unsigned N_IN      = 128,    // Size of the input side
    parameter int unsigned N_HIDDEN  = 64,     // Size of the output side (neurons)
    parameter int unsigned N_LAYERS  = 3,      // Total layers to process
    parameter int unsigned P         = 4       // Parallelism factor (neurons per cycle)
)(
    input  logic clk,          // System clock
    input  logic rst_n,        // Asynchronous reset (active low)

    // Layer control
    input  logic [$clog2(N_LAYERS)-1:0] layer_idx, // Which layer are we calculating?

    // Start trigger
    input  logic start_compute, // Pulse to start processing the current input vector

    // Input Vector (Parallel bus from input_buffer or activation memory)
    input  logic signed [N_IN*DATA_W-1:0] invec_bus,

    // Weight memory interface
    output logic [$clog2(N_LAYERS*N_HIDDEN*N_IN)-1:0] wmem_raddr, // Read address
    input  logic signed [DATA_W-1:0] wmem_rdata,                 // Weight data

    // Output stream (Target: ReLU / Next Layer / Final AXI adapter)
    output logic signed [(2*DATA_W)+$clog2((N_IN>1)?N_IN:2)-1:0] out_data,
    output logic out_valid,
    input  logic out_ready,

    // Status signals
    output logic busy,       // Engine is currently occupied
    output logic layer_done  // Pulse when all neurons of current layer are done
);


    // Local parameters for bit-width calculations
    localparam int IN_CNT_W = $clog2((N_IN>1)?N_IN:2);
    localparam int ACC_W    = (2*DATA_W) + IN_CNT_W; // Accumulator bit-width
    localparam int BIT_W    = $clog2((PRECISION>1)?PRECISION:2);
    localparam int HID_W    = $clog2((N_HIDDEN>1)?N_HIDDEN:2);
    localparam int P_W      = $clog2((P>1)?P:2);
    localparam int WMEM_ADDR_W = $clog2(N_LAYERS * N_HIDDEN * N_IN);
    // Stride to skip layers in a flattened weight memory
    localparam logic [WMEM_ADDR_W-1:0] LSTRIDE  = N_HIDDEN * N_IN;

    // FSM State Definitions
    typedef enum logic [1:0] { 
        IDLE,   // Waiting for data
        PROC,   // Processing bit-serial multiplication
        STREAM  // Streaming output activations
    } state_t;
    state_t state, state_n;

  
    // Control Registers & Counters
    logic [HID_W-1:0]    cur_hidden; // Current neuron block index
    logic [IN_CNT_W-1:0] cur_input;  // Current input element index
    logic [BIT_W-1:0]    bit_idx;    // Current bit position for bit-serial

    logic                bit_active;       // High when bit-serial loop is running
    logic                mem_read_pending; // High during multi-cycle weight fetch
    logic                mem_wait;         // Pipeline stall for BRAM latency
    logic [P_W-1:0]      mem_lane;         // Current parallel lane for weight fetch

    // Working Registers
    logic signed [DATA_W-1:0] a_val;             // Cached input element
    logic signed [DATA_W-1:0] abs_b [P];        // absolute weight values for serial processing
    logic                     sign_prod [P];    // sign bits for final accumulation
    logic signed [ACC_W-1:0]  partial [P];      // inter-cycle partial sums
    logic signed [ACC_W-1:0]  hidden_accum [N_HIDDEN]; // Main accumulator array

    // Output Completion tracking
    logic [HID_W:0]   out_index; // Counter for STREAM state


   
    // Bit-Serial Arithmetic Logic
    // Convert input data to absolute and shift it according to current bit index
    wire signed [DATA_W-1:0] abs_a =
        a_val[DATA_W-1] ? -a_val : a_val;

    wire signed [ACC_W-1:0] shifted_abs_a =
        $signed({{(ACC_W-DATA_W){1'b0}}, abs_a}) << bit_idx;


    // FSM: Next-state combinatorial logic
    always_comb begin
        state_n = state;
        case (state)
            IDLE:   if (start_compute) state_n = PROC;

            PROC: begin
                // Transition to STREAM when all input pixels and all hidden neurons are processed
                if (bit_active &&
                    (bit_idx == PRECISION-1) &&
                    (cur_input + 1 >= N_IN) &&
                    (cur_hidden + P >= N_HIDDEN))
                    state_n = STREAM;
            end

            STREAM: begin
                // Return to IDLE once all neurons have been flushed through out_data
                if (out_index >= N_HIDDEN)
                    state_n = IDLE;
            end

            default: state_n = IDLE;
        endcase
    end

    
    // Main Sequential Processing Block
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Hardware reset of all control registers
            state <= IDLE;
            busy  <= 1'b0;
            layer_done <= 1'b0;
            cur_hidden <= '0;
            cur_input  <= '0;
            bit_idx    <= '0;
            bit_active <= 1'b0;
            mem_read_pending <= 1'b0;
            mem_wait         <= 1'b0;
            mem_lane         <= '0;
            out_valid     <= 1'b0;
            out_index     <= '0;
            out_data      <= '0;
            a_val      <= '0;
            wmem_raddr <= '0;

            // Clear accumulators
            for (int i=0; i<N_HIDDEN; i++)
                hidden_accum[i] <= '0;

            // Clear pipeline registers
            for (int i=0; i<P; i++) begin
                abs_b[i]     <= '0;
                sign_prod[i] <= '0;
                partial[i]   <= '0;
            end

        end else begin
            state <= state_n;
            busy  <= (state_n != IDLE);

            case (state)

                // ---------------- IDLE ----------------
                IDLE: begin
                    cur_hidden   <= '0;
                    cur_input    <= '0;
                    out_index    <= '0;
                    out_valid    <= 1'b0;
                    bit_active   <= 1'b0;
                    mem_read_pending <= 1'b0;
                    layer_done <= 1'b0;

                    // Prepare accumulators when a new computation requests starts
                    if (start_compute) begin
                        for (int i=0; i<N_HIDDEN; i++)
                            hidden_accum[i] <= '0;
                    end
                end

                // ---------------- PROC (The Core Math Loop) ----------------
                PROC: begin
                    /**
                     * STAGE 1: Memory Fetch
                     * Fetch weights for P neurons in parallel for the current input element.
                     */
                    if (!bit_active && !mem_read_pending &&
                        cur_hidden < N_HIDDEN) begin

                        mem_read_pending <= 1'b1;
                        mem_lane <= '0;
                        mem_wait <= 1'b1; // Wait for BRAM read latency

                        // Grab the current input word
                        a_val <= invec_bus[cur_input*DATA_W +: DATA_W];
                        // Address calculation for flattened memory: Layer Offset + Hidden Offset + Input Offset
                        wmem_raddr <= (layer_idx * LSTRIDE)+(cur_hidden * N_IN) + cur_input;
                    end

                    // Iterate through P parallel lanes to fetch weights
                    if (mem_read_pending) begin
                        if (mem_wait) begin
                            mem_wait <= 1'b0; // Latency cycle
                        end else begin
                            // Capture weight and absolute/sign prep
                            abs_b[mem_lane] <=
                                wmem_rdata[DATA_W-1] ? -wmem_rdata : wmem_rdata;

                            sign_prod[mem_lane] <=
                                a_val[DATA_W-1] ^ wmem_rdata[DATA_W-1];

                            // If we still need more lanes for this block, continue fetching
                            if ((mem_lane + 1 < P) &&
                                (cur_hidden + mem_lane + 1 < N_HIDDEN)) begin
                                mem_lane <= mem_lane + 1'b1;
                                mem_wait <= 1'b1;
                                wmem_raddr <=
                                  (layer_idx * LSTRIDE) + (cur_hidden + mem_lane + 1) * N_IN + cur_input ;
                            end else begin
                                // All P weights fetched, start the bit-serial cycle
                                mem_read_pending <= 1'b0;
                                bit_active <= 1'b1;
                                bit_idx <= '0;
                                for (int i=0; i<P; i++)
                                    partial[i] <= '0;
                            end
                        end
                    end

                    /**
                     * STAGE 2: Bit-Serial Multi-Accumulate
                     * Instead of using full multipliers, we iterate bit-by-bit over the weight.
                     * DATA_W cycles of Shift-and-Add per weight block.
                     */
                    if (bit_active) begin
                        for (int unsigned i=0; i<P; i++) begin
                            if (cur_hidden + i < N_HIDDEN) begin
                                // If the current bit of weight is 1, add the shifted input value
                                if (abs_b[i][bit_idx])
                                    partial[i] <= partial[i] + shifted_abs_a;
                            end
                        end

                        // Check for completion of bit-cycle for current input element
                        if (bit_idx == PRECISION-1) begin
                            bit_active <= 1'b0;

                            // Final Accumulation into large sum-of-products array
                            for (int unsigned i=0; i<P; i++) begin
                                if (cur_hidden + i < N_HIDDEN) begin
                                    automatic logic [ACC_W-1:0] final_p;
                                    // Combine final bit with sign correction
                                    final_p =
                                        abs_b[i][bit_idx] ?
                                        (partial[i] + shifted_abs_a) :
                                        partial[i];

                                    // Add or Subtract based on the product's XORed sign bit
                                    hidden_accum[cur_hidden+i] <=
                                        sign_prod[i] ?
                                        (hidden_accum[cur_hidden+i] - final_p) :
                                        (hidden_accum[cur_hidden+i] + final_p);
                                end
                            end

                            // Boundary Check: Move to next input or next neuron block?
                            if (cur_input + 1 >= N_IN) begin
                                cur_input  <= '0;
                                cur_hidden <= cur_hidden + P;
                            end else begin
                                cur_input <= cur_input + 1'b1;
                            end
                        end else begin
                            // Increment bit index for more precision
                            bit_idx <= bit_idx + 1'b1;
                        end
                    end
                end

                /**
                 * ---------------- STREAM ----------------
                 * Flushes the final neuron values to the output AXI bus.
                 * Includes handshake logic (out_ready/out_valid).
                 */
                STREAM: begin
                    if (out_index < N_HIDDEN) begin
                        if (!out_valid) begin
                            // Load first available neuron to the bus
                            out_data  <= hidden_accum[out_index[HID_W-1:0]];
                            out_valid <= 1'b1;
                        end
                        else if (out_ready) begin
                            // Successfully transferred! Move to next neuron
                            if (out_index + 1 < N_HIDDEN) begin
                                out_index <= out_index + 1'b1;
                                out_data  <= hidden_accum[out_index[HID_W-1:0] + 1'b1];
                                out_valid <= 1'b1;
                            end else begin
                                // All sent. Pulse layer_done.
                                out_index  <= out_index + 1'b1;
                                out_valid  <= 1'b0;
                                layer_done <= 1'b1;
                            end
                        end
                    end else begin
                        // Cleanup and return to IDLE
                        out_valid  <= 1'b0;
                        layer_done <= 1'b0;
                        state      <= IDLE; 
                    end
                end

            endcase
        end
    end

endmodule

