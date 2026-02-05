`timescale 1ns/1ps

/**
 * Module: input_buffer
 * Description: Buffered AXI-Stream receiver that captures incoming serial data
 *              and packs it into a wide parallel bus for the MAC engine.
 *              Handles flow control via 'busy' and validates vector completeness via 'tlast'.
 */
module input_buffer #(
    parameter int DATA_W = 16, // Width of each input element (e.g., 16-bit signed)
    parameter int N_IN   = 128 // Dimensions of the input vector (e.g., 128 elements)
)(
    input  logic clk,          // Main system clock
    input  logic rst_n,        // Asynchronous reset (active low)

    // Streaming input (Slave AXI-Stream like interface)
    input  logic signed [DATA_W-1:0] data_in,       // Incoming data word
    input  logic                     data_in_valid, // Valid signal for incoming word

    // AXI end-of-vector marker (tlast)
    input  logic                     vector_last,   // Asserted on the last word of a vector

    // MAC status (Flow control backpressure)
    input  logic                     busy,          // High if downstream MAC is processing

    // packed output vector for MAC
    output logic signed [N_IN*DATA_W-1:0] invec_bus, // Fully assembled parallel vector

    // end-of-vector pulse (1 cycle)
    output logic                     vector_done     // Pulse indicating a full vector is ready
);

     
    // Local parameters
    // Calculate the width needed for the write pointer
    localparam int CNT_W = (N_IN > 1) ? $clog2(N_IN) : 1;

     
    // Internal storage
    // write pointer to track incoming words
    logic [CNT_W-1:0]              wr_ptr;
    // Memory array to store words until the vector is complete
    logic signed [DATA_W-1:0]      inbuf [0:N_IN-1];

    integer i;

     
    // Pack buffer into wide bus
    // This combinational block maps the internal array to a flat output port
    genvar gi;
    generate
        for (gi = 0; gi < N_IN; gi++) begin : PACK
            // Pack each DATA_W-bit word into its corresponding slot in the parallel bus
            assign invec_bus[(gi+1)*DATA_W-1 -: DATA_W] = inbuf[gi];
        end
    endgenerate

    // Input buffering and vector completion logic
     
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset state: clear pointers and the entire buffer
            wr_ptr      <= '0;
            vector_done <= 1'b0;

            for (i = 0; i < N_IN; i++)
                inbuf[i] <= '0;

        end else begin
            // Default: clear the one-cycle 'done' pulse
            vector_done <= 1'b0; 

            // Stall input buffer while MAC is busy (Backpressure)
            // and write only when valid data is present on the bus
            if (!busy && data_in_valid) begin
                // Store incoming word at the current pointer position
                inbuf[wr_ptr] <= data_in;

                /**
                 * Vector Assembly State Machine Logic:
                 * Case 1: Reached end of buffer AND TLAST is correctly asserted.
                 * Case 2: Reached end of buffer but TLAST is missing (Error).
                 * Case 3: TLAST arrived early before buffer is full (Error).
                 * Case 4: Normal increment.
                 */
                if ((wr_ptr == N_IN-1) && vector_last) begin
                    // Success: Full vector received correctly
                    wr_ptr      <= '0;
                    vector_done <= 1'b1;   // Trigger the computation in the next cycle
                end 
                
                else if (wr_ptr == N_IN-1) begin
                    // Error: Buffer is full but sender didn't signal the last word
                    wr_ptr <= '0;
`ifndef SYNTHESIS
                    $error("[Time %0t] Buffer full but vector_last not asserted! Vector discarded.", $time);
`endif
                end 
                
                else if (vector_last) begin
                    // Error: Sender signaled end of vector but we were still expecting words
                    wr_ptr <= '0;
`ifndef SYNTHESIS
                    $error("[Time %0t] vector_last arrived at position %0d (expected %0d). Incomplete vector discarded.", 
                           $time, wr_ptr, N_IN-1);
`endif
                end 
                
                else begin
                    // Normal Operation: Simply increment to next slot
                    wr_ptr <= wr_ptr + 1'b1;
                end
            end
        end
    end

endmodule
