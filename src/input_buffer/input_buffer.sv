`timescale 1ns/1ps

module input_buffer #(
    parameter int DATA_W = 16,
    parameter int N_IN   = 128
)(
    input  logic clk,
    input  logic rst_n,

    // streaming input
    input  logic signed [DATA_W-1:0] data_in,
    input  logic                     data_in_valid,

    // MAC status
    input  logic                     busy,

    // packed output vector for MAC
    output logic signed [N_IN*DATA_W-1:0] invec_bus,

    // end-of-vector pulse (1 cycle)
    output logic                     vector_done
);

   
    // Local parameters

    localparam int CNT_W = (N_IN > 1) ? $clog2(N_IN) : 1;


    // Internal storage
    logic [CNT_W-1:0]              wr_ptr;
    logic signed [DATA_W-1:0]      inbuf [0:N_IN-1];

    integer i;


    // Pack inbuf[] into wide output bus
    genvar gi;
    generate
        for (gi = 0; gi < N_IN; gi++) begin : PACK
            assign invec_bus[(gi+1)*DATA_W-1 -: DATA_W] = inbuf[gi];
        end
    endgenerate


    // Input buffering and vector completion logic
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            wr_ptr      <= '0;
            vector_done <= 1'b0;

            for (i = 0; i < N_IN; i++)
                inbuf[i] <= '0;

        end else begin
            vector_done <= 1'b0;

            // Stall input buffer while MAC is busy
            if (!busy && data_in_valid) begin
                inbuf[wr_ptr] <= data_in;

                if (wr_ptr == N_IN-1) begin
                    wr_ptr      <= '0;
                    vector_done <= 1'b1;   // 1-cycle pulse
                end
                else begin
                    wr_ptr <= wr_ptr + 1'b1;
                end
            end
        end
    end

endmodule
