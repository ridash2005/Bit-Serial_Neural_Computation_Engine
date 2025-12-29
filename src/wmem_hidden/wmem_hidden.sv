`timescale 1ns/1ps

module wmem_hidden #(
    parameter int DATA_W   = 16,
    parameter int N_IN     = 128,
    parameter int N_HIDDEN = 64
)(
    input  logic clk,
    input  logic rst_n,


    // Write port (from host / loader)

    input  logic                           w_wr_en,
    input  logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h,
    input  logic [$clog2((N_IN>1)?N_IN:2)-1:0]         w_addr_i,
    input  logic signed [DATA_W-1:0]                  w_data,


    // Read port (from MAC engine)

    input  logic [$clog2(((N_HIDDEN*N_IN)>1)?(N_HIDDEN*N_IN):2)-1:0] raddr,
    output logic signed [DATA_W-1:0]                                 rdata
);


    // Local parameters
    localparam int WMEM_SIZE   = N_HIDDEN * N_IN;
    localparam int WMEM_ADDR_W = $clog2((WMEM_SIZE>1)?WMEM_SIZE:2);


    // Weight storage (BRAM)
    (* ram_style = "block" *)
    logic signed [DATA_W-1:0] mem [0:WMEM_SIZE-1];


    // Write data pipeline 
    logic signed [DATA_W-1:0] w_data_reg;
    logic [WMEM_ADDR_W-1:0]   w_addr_reg;
    logic                     w_en_reg;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            w_data_reg <= '0;
            w_addr_reg <= '0;
            w_en_reg   <= 1'b0;
        end else begin
            w_data_reg <= w_data;
            w_addr_reg <= (w_addr_h * N_IN) + w_addr_i; // Flatten and pipe
            w_en_reg   <= w_wr_en;
        end
    end


    // BRAM Port
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            rdata <= '0;
        end else begin
            if (w_en_reg) begin
                mem[w_addr_reg] <= w_data_reg;
            end
            rdata <= mem[raddr];
        end
    end
endmodule
