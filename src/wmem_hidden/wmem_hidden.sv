`timescale 1ns/1ps

module wmem_hidden #(
    parameter int DATA_W   = 16,
    parameter int N_IN     = 128,
    parameter int N_HIDDEN = 64,
    parameter int N_LAYERS = 3
)(
    input  logic clk,
    input  logic rst_n,

    // ---------------- WRITE PORT (HOST) ----------------
    input  logic                                   w_wr_en,
    input  logic [$clog2((N_LAYERS>1)?N_LAYERS:2)-1:0] w_addr_l,
    input  logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h,
    input  logic [$clog2((N_IN>1)?N_IN:2)-1:0]         w_addr_i,
    input  logic signed [DATA_W-1:0]                   w_data,

    // ---------------- READ PORT (MAC) ----------------
    input  logic [$clog2((N_LAYERS*N_HIDDEN*N_IN>1)?
                          (N_LAYERS*N_HIDDEN*N_IN):2)-1:0] raddr,
    output logic signed [DATA_W-1:0]                         rdata
);

    /* ---------------- LOCAL PARAMETERS ---------------- */

    localparam int WMEM_SIZE   = N_LAYERS * N_HIDDEN * N_IN;
    localparam int WMEM_ADDR_W = $clog2((WMEM_SIZE>1)?WMEM_SIZE:2);

    localparam int LSTRIDE = N_HIDDEN * N_IN;

    /* ---------------- MEMORY ---------------- */

    (* ram_style = "block" *)
    logic signed [DATA_W-1:0] mem [0:WMEM_SIZE-1];

    /* ---------------- WRITE PIPELINE ---------------- */

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
            w_addr_reg <= (w_addr_l * LSTRIDE) +
                          (w_addr_h * N_IN) +
                           w_addr_i;
            w_en_reg   <= w_wr_en;
        end
    end

    /* ---------------- BRAM PORT ---------------- */

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            rdata <= '0;
        end else begin
            if (w_en_reg)
                mem[w_addr_reg] <= w_data_reg;

            rdata <= mem[raddr];
        end
    end

endmodule
