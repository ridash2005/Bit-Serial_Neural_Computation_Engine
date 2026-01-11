`timescale 1ns/1ps

/**
 * Module: relu_activation
 * Description: Implements the Rectified Linear Unit (ReLU) activation function.
 *              Output = MAX(0, Input).
 *              Fully AXI-Stream compliant with integrated skid-buffer 
 *              for zero-loss backpressure handling.
 */
module relu_activation #(
    parameter int ACC_W = 64   // Bit-width of the incoming accumulator value
)(
    input  logic                    clk,   // system clock
    input  logic                    rst_n, // asynchronous reset

    // Slave AXI-Stream Interface (Incoming from MAC)
    input  logic signed [ACC_W-1:0] in_data,  // raw sum-of-products
    input  logic                    in_valid, // source valid pulse
    output logic                    in_ready, // backpressure to MAC

    // Master AXI-Stream Interface (Outgoing to Next Layer / Output)
    input  logic                    out_ready, // backpressure from downstream
    output logic signed [ACC_W-1:0] out_data,  // clipped activation
    output logic                    out_valid  // master valid strobe
);

    /**
     * Skid-Buffer / Registration Logic:
     * This register holds a single activation value to allow for a 
     * clean AXI-Stream handshake without timing critical paths.
     */
    logic signed [ACC_W-1:0] out_data_reg;
    logic                    out_valid_reg;
    
    /**
     * Flow Control Logic:
     * We can accept a new word IF the current output register is 
     * either empty (not valid) OR is being consumed by the downstream 
     * (out_ready is high).
     */
    assign in_ready = !out_valid_reg || out_ready;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // asynchronous reset state
            out_data_reg  <= '0;
            out_valid_reg <= 1'b0;
        end else begin
            // Transfer logic: Update when we are ready to output
            if (out_ready || !out_valid_reg) begin
                if (in_valid) begin
                    /**
                     * The ReLU mathematical function:
                     * If x >= 0, return x.
                     * If x <  0, return 0. (Active clipping)
                     */
                    out_data_reg  <= (in_data < 0) ? '0 : in_data;
                    out_valid_reg <= 1'b1;
                end else begin
                    // Clear valid if no input is arriving and current is sent
                    out_valid_reg <= 1'b0;
                end
            end
            // else: Downstream is NOT ready and register is full.
            // We MUST hold the current out_data_reg stable (skid buffer).
        end
    end
    
    // Continuous assignment to output ports
    assign out_data  = out_data_reg;
    assign out_valid = out_valid_reg;

endmodule
