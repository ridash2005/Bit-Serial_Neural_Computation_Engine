`timescale 1ns/1ps

/**
 * Module: tb_wmem_hidden
 * Description: Testbench for the Pipelined Weight Memory (BRAM).
 *              Verifies that the address flattening (L, H, I) logic 
 *              matches the flat read addressing used by the MAC engine.
 */
module tb_wmem_hidden;

    // 1. Parameters & Signal Declarations
    parameter int DATA_W   = 16;
    parameter int N_IN     = 8;  
    parameter int N_HIDDEN = 4;
    parameter int N_LAYERS = 3;
    
    // Width derived from parameters
    localparam int WMEM_SIZE = N_LAYERS * N_HIDDEN * N_IN;
    localparam int ADDR_L_W  = $clog2((N_LAYERS>1)?N_LAYERS:2);
    localparam int ADDR_H_W  = $clog2((N_HIDDEN>1)?N_HIDDEN:2);
    localparam int ADDR_I_W  = $clog2((N_IN>1)?N_IN:2);
    localparam int RADDR_W   = $clog2((WMEM_SIZE>1)?WMEM_SIZE:2);

    logic clk;
    logic rst_n;

    // Write Interface (Loading side)
    logic                     w_wr_en;
    logic [ADDR_L_W-1:0]      w_addr_l;
    logic [ADDR_H_W-1:0]      w_addr_h;
    logic [ADDR_I_W-1:0]      w_addr_i;
    logic signed [DATA_W-1:0] w_data;

    // Read Interface (MAC Engine side)
    logic [RADDR_W-1:0]       raddr;
    logic signed [DATA_W-1:0] rdata;

    /**
     * Scoreboard (Shadow Memory)
     * We keep a software array in the testbench that mimics the expected 
     * contents of the hardware memory to detect any addressing errors.
     */
    logic signed [DATA_W-1:0] shadow_mem [WMEM_SIZE];
    
    int error_count = 0;
    int rl=0, rh=0, ri=0, rval=0, addr_flat=0;  


    // 2. DUT (Device Under Test) Instantiation
    wmem_hidden #(
        .DATA_W(DATA_W),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .N_LAYERS(N_LAYERS)
    ) dut (.*);


    // 3. Clock Generation (100 MHz)
    initial begin
        clk = 0;
        forever #5 clk = ~clk; 
    end


    // 4. Test Stimulus Executive Sequence
    initial begin
        // Initialize interface to clean state
        rst_n    = 0;
        w_wr_en  = 0;
        w_addr_l = 0;
        w_addr_h = 0;
        w_addr_i = 0;
        w_data   = 0;
        raddr    = 0;
        
        // Clear shadow memory
        for(int j=0; j<WMEM_SIZE; j++) shadow_mem[j] = 0;

        repeat(5) @(posedge clk);
        rst_n = 1; // Release reset
        @(posedge clk);

        // --- TEST 1: Sequential Filling of All Memory Locations ---
        $display("\n--- TEST 1: Sequential Layer-by-Layer Weight Load ---");
        for (int l = 0; l < N_LAYERS; l++) begin
            for (int h = 0; h < N_HIDDEN; h++) begin
                for (int i = 0; i < N_IN; i++) begin
                    // Use a unique pattern for each location for easy debugging
                    write_weight(l, h, i, $signed(l*100 + h*10 + i + 1));
                end
            end
        end

        // Wait for last write pipeline to settle
        repeat(2) @(posedge clk);

        // --- TEST 2: Verify Flat Read Accuracy ---
        $display("\n--- TEST 2: Linear Verification using Flat Addresses ---");
        for (int addr = 0; addr < WMEM_SIZE; addr++) begin
            check_read(addr);
        end

        // --- TEST 3: Random Access Stress Test ---
        $display("\n--- TEST 3: Random Stress (Sparse Updates) ---");
        repeat(50) begin
              rl   = $urandom_range(0, N_LAYERS-1);
              rh   = $urandom_range(0, N_HIDDEN-1);
              ri   = $urandom_range(0, N_IN-1);
              rval = $urandom_range(-32768, 32767); // full 16-bit range
              addr_flat = (rl * N_HIDDEN * N_IN) + (rh * N_IN) + ri;
            
            write_weight(rl, rh, ri, rval);
            check_read(addr_flat);
        end

        // Final Scoreboard Report
        $display("\n==================================================");
        $display("   WEIGHT MEMORY VERIFICATION SUMMARY");
        if (error_count == 0) begin
            $display("   RESULT: SUCCESS (0 errors)");
        end else begin
            $display("   RESULT: FAILED (%0d errors encountered)", error_count);
        end
        $display("==================================================\n");
        
        $finish;
    end


    // 5. HELPER TASKS for Memory Interaction

    /**
     * Task: write_weight
     * Handles the 2-cycle latency of the hardware write pipeline.
     */
    task automatic write_weight(
        input [ADDR_L_W-1:0] l,
        input [ADDR_H_W-1:0] h, 
        input [ADDR_I_W-1:0] i, 
        input signed [DATA_W-1:0] data
    );
        automatic int flat_addr = (l * N_HIDDEN * N_IN) + (h * N_IN) + i;
        begin
            // T=0: Apply inputs to the DUT pins
            w_addr_l <= l;
            w_addr_h <= h;
            w_addr_i <= i;
            w_data   <= data; 
            w_wr_en  <= 1;
            
            @(posedge clk);  // T=1: Data captured by DUT's internal registers
            w_wr_en <= 0;    // Release write strobe
            
            @(posedge clk);  // T=2: Data committed to internal RAM array
            
            // Sync the scoreboard to the hardware's expected state
            shadow_mem[flat_addr] = data;
        end
    endtask


    /**
     * Task: check_read
     * Handles the synchronous read latency (rdata is valid 1 cycle after raddr).
     */
    task automatic check_read(input [RADDR_W-1:0] addr);
        logic signed [DATA_W-1:0] expected;
        begin
            expected = shadow_mem[addr];
            raddr <= addr;      // Set the address probe
            
            @(posedge clk);     // BRAM read latency (1 cycle)
            #1;                 // Offset slightly to sample after the transition
            
            if (rdata !== expected) begin
                $error("[FAIL] Addr %0d: Expected %h, Got %h", addr, expected, rdata);
                error_count++;
            end
        end
    endtask

endmodule
