`timescale 1ns/1ps

/**
 * Module: wmem_hidden
 * Description: Flattened Block RAM (BRAM) for storing neural network weights.
 *              Organized by [Layer][Hidden Neuron][Input Feature].
 *              Optimized for high-frequency FPGA synthesis using pipelined writes.
 */
module wmem_hidden #(
    parameter int DATA_W   = 16, // bit-width of each weight
    parameter int N_IN     = 128, // input side dimension
    parameter int N_HIDDEN = 64,  // hidden side dimension
    parameter int N_LAYERS = 3    // supports stacking multiple layers in one BRAM
)(
    input  logic clk,   // system clock
    input  logic rst_n, // asynchronous reset

    /**
     * Write Port: Port used by the host or loader (e.g., AXI-Lite bridge)
     * to populate the weights before computation starts.
     */
    input  logic                                       w_wr_en,   // write enable
    input  logic [$clog2((N_LAYERS > 1) ? N_LAYERS : 2)-1:0] w_addr_l, // layer index
    input  logic [$clog2((N_HIDDEN > 1) ? N_HIDDEN : 2)-1:0] w_addr_h, // hidden index
    input  logic [$clog2((N_IN > 1) ? N_IN : 2)-1:0]         w_addr_i, // input index
    input  logic signed [DATA_W-1:0]                  w_data,   // weight data to write


    /**
     * Read Port: Shared port used by the MAC engine during inference.
     * Flat address space [0 : (L*H*I)-1]
     */
    input  logic [$clog2((N_LAYERS*N_HIDDEN*N_IN > 1) ? (N_LAYERS*N_HIDDEN*N_IN) : 2)-1:0] raddr,
    output logic signed [DATA_W-1:0]  rdata
);


    // Address spacing and stride calculations
    localparam int WMEM_SIZE = N_LAYERS * N_HIDDEN * N_IN;
    localparam int WMEM_ADDR_W = $clog2((WMEM_SIZE>1)?WMEM_SIZE:2);
    localparam int LSTRIDE = N_HIDDEN * N_IN; // dimension of a single layer footprint

    /**
     * Weight Storage (BRAM Inference)
     * The 'ram_style = "block"' attribute guides tools (like Vivado) 
     * to use dedicated BRAM resources instead of expensive LUT-RAM.
     */
    (* ram_style = "block" *)
    logic signed [DATA_W-1:0] mem [0:WMEM_SIZE-1];


    // Write pipeline registers to improve timing on high-utilized FPGAs
    logic signed [DATA_W-1:0] w_data_reg;
    logic [WMEM_ADDR_W-1:0]   w_addr_reg;
    logic                     w_en_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset write pipeline
            w_data_reg <= '0;
            w_addr_reg <= '0;
            w_en_reg   <= 1'b0;
        end else begin
            w_data_reg <= w_data;
            // Flatten the hierarchical N-dimensional address into a linear address
            // Formula: (Layer * Stride) + (Neuron * Width) + offset
            w_addr_reg <= (w_addr_l * LSTRIDE) + (w_addr_h * N_IN) + w_addr_i; 
            w_en_reg   <= w_wr_en;
        end
    end


    /**
     * BRAM Hardware Port Logic:
     * Synchronous read/write implementation.
     */
    always_ff @(posedge clk) begin
        if (w_en_reg) begin
            // Write to memory array
            mem[w_addr_reg] <= w_data_reg;
        end
        // Synchronous read (registered output for better timing)
        rdata <= mem[raddr];
    end

endmodule

