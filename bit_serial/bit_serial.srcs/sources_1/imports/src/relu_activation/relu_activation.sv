`timescale 1ns/1ps

module relu_activation #(
    parameter int ACC_W = 40   // width of MAC output
)(
    input  logic                    clk,
    input  logic                    rst_n,

    input  logic signed [ACC_W-1:0] in_data,
    input  logic                    in_valid,

    output logic signed [ACC_W-1:0] out_data,
    output logic                    out_valid
);

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            out_data  <= '0;
            out_valid <= 1'b0;
        end else begin
            out_valid <= in_valid;

            if (in_valid) begin
                if (in_data < 0)
                    out_data <= '0;
                else
                    out_data <= in_data;
            end
        end
    end

endmodule
