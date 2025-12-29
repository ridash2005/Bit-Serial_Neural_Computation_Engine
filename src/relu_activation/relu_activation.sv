`timescale 1ns/1ps

module relu_activation #(
    parameter int ACC_W = 64   // width of MAC output
)(
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic signed [ACC_W-1:0] in_data,
    input  logic                    in_valid,
    output logic                    in_ready,    // Added for backpressure
    input  logic                    out_ready,
    output logic signed [ACC_W-1:0] out_data,
    output logic                    out_valid
);
    // Internal register to hold data if downstream is not ready
    logic signed [ACC_W-1:0] out_data_reg;
    logic                    out_valid_reg;
    
    // Can accept new input when output is not valid or being consumed
    assign in_ready = !out_valid_reg || out_ready;
    
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            out_data_reg  <= '0;
            out_valid_reg <= 1'b0;
        end else begin
            // Only update output when downstream is ready or no valid data is being held
            if (out_ready || !out_valid_reg) begin
                if (in_valid) begin
                    out_data_reg  <= (in_data < 0) ? '0 : in_data;
                    out_valid_reg <= 1'b1;
                end else begin
                    out_valid_reg <= 1'b0;
                end
            end
            // else hold previous output until ready
        end
    end
    
    assign out_data  = out_data_reg;
    assign out_valid = out_valid_reg;
endmodule