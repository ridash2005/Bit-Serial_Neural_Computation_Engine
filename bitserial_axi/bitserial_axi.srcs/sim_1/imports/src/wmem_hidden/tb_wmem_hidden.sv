`timescale 1ns/1ps

module tb_wmem_hidden;

    // 1. Parameters & Signals

    parameter int DATA_W   = 16;
    parameter int N_IN     = 8;  
    parameter int N_HIDDEN = 4;
    
    localparam int WMEM_SIZE = N_HIDDEN * N_IN;
    // Fixed: Match module's address width calculation
    localparam int ADDR_H_W  = $clog2((N_HIDDEN>1)?N_HIDDEN:2);
    localparam int ADDR_I_W  = $clog2((N_IN>1)?N_IN:2);
    localparam int RADDR_W   = $clog2((WMEM_SIZE>1)?WMEM_SIZE:2);

    logic clk;
    logic rst_n;

    // Write Port
    logic                     w_wr_en;
    logic [ADDR_H_W-1:0]      w_addr_h;
    logic [ADDR_I_W-1:0]      w_addr_i;
    logic signed [DATA_W-1:0] w_data;

    // Read Port
    logic [RADDR_W-1:0]       raddr;
    logic signed [DATA_W-1:0] rdata;

    // Scoreboard: A local array to mimic expected memory state
    logic signed [DATA_W-1:0] shadow_mem [WMEM_SIZE];
    
    int error_count = 0;
    int rh=0, ri=0, rval=0, addr_flat=0;  

    // 2. DUT Instantiation

    wmem_hidden #(
        .DATA_W(DATA_W),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN)
    ) dut (.*);


    // 3. Clock Generation

    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100 MHz
    end


    // 4. Test Stimulus

    initial begin
        //$dumpfile("wmem_dump.vcd");
        //$dumpvars(0, tb_wmem_hidden);

        // Initialize signals
        rst_n    = 0;
        w_wr_en  = 0;
        w_addr_h = 0;
        w_addr_i = 0;
        w_data   = 0;
        raddr    = 0;
        
        // Initialize scoreboard to match DUT reset state
        for(int j=0; j<WMEM_SIZE; j++) shadow_mem[j] = 0;

        repeat(5) @(posedge clk);
        rst_n = 1;
        @(posedge clk);

        // --- TEST 1: Sequential Write (Load Weights) ---
        $display("--- Test 1: Loading Weights ---");
        for (int h = 0; h < N_HIDDEN; h++) begin
            for (int i = 0; i < N_IN; i++) begin
                write_weight(h, i, $signed(h*10 + i + 1));
            end
        end

        // Allow final writes to complete (write_weight already includes proper delays)
        repeat(2) @(posedge clk);

        // --- TEST 2: Verify Read Latency and Data ---
        $display("--- Test 2: Verifying Reads ---");
        for (int addr = 0; addr < WMEM_SIZE; addr++) begin
            check_read(addr);
        end

        // --- TEST 3: Random Access Write/Read ---
        $display("--- Test 3: Random Access ---");
        repeat(15) begin
              rh   = $urandom_range(0, N_HIDDEN-1);
              ri   = $urandom_range(0, N_IN-1);
              rval = $urandom_range(-500, 500);
              addr_flat = rh * N_IN + ri;
            
            $display("[Time %0t] Writing to [h=%0d, i=%0d] addr=%0d value=%0d", 
                     $time, rh, ri, addr_flat, rval);
            
            write_weight(rh, ri, rval);
            
            // No additional wait needed - write_weight handles timing
            check_read(addr_flat);
        end

        // --- TEST 4: Back-to-back writes to same location ---
        $display("--- Test 4: Overwrite Test ---");
        write_weight(0, 0, 100);
        write_weight(0, 0, 200);
        write_weight(0, 0, 300);
        repeat(2) @(posedge clk);
        check_read(0); // Should read 300

        // --- TEST 5: Write and immediate read to different addresses ---
        $display("--- Test 5: Concurrent Access Test ---");
        write_weight(1, 1, 111);
        // Start reading from different address while write completes
        check_read(2 * N_IN + 2);
        check_read(1 * N_IN + 1); // Now read the address we just wrote

        // Final Report
        $display("\n========================================");
        if (error_count == 0) begin
            $display("All tests PASSED!");
        end else begin
            $display("Tests FAILED with %0d errors", error_count);
        end
        $display("========================================\n");
        
        $finish;
    end


    // Helper Tasks

    // Fixed: Properly handle 2-cycle write pipeline delay
    task automatic write_weight(
        input [ADDR_H_W-1:0] h, 
        input [ADDR_I_W-1:0] i, 
        input signed [DATA_W-1:0] data
    );
        automatic int flat_addr = h * N_IN + i;
        begin
            // Cycle 0: Apply write inputs
            w_addr_h <= h;
            w_addr_i <= i;
            w_data   <= data; 
            w_wr_en  <= 1;
            
            @(posedge clk);  // Cycle 1: Data enters pipeline registers (w_data_reg, etc.)
            w_wr_en <= 0;    // De-assert write enable
            
            @(posedge clk);  // Cycle 2: Data is written to mem[]
            
            // Now update shadow memory to reflect the completed write
            shadow_mem[flat_addr] = data;
            
            $display("[Time %0t] Write completed: Addr %0d = %h", $time, flat_addr, data);
        end
    endtask

    // Fixed: Properly handle synchronous BRAM read with 1-cycle latency
    task automatic check_read(input [RADDR_W-1:0] addr);
        logic signed [DATA_W-1:0] expected;
        begin
            expected = shadow_mem[addr];
            raddr <= addr;      // Apply read address
            
            @(posedge clk);     // Wait 1 cycle for BRAM read latency
            #1;                 // Small delta delay to sample after clock edge
            
            if (rdata !== expected) begin
                $error("[Time %0t] Read Mismatch at Addr %0d! Expected: %h, Got: %h", 
                        $time, addr, expected, rdata);
                error_count++;
            end else begin
                $display("[Time %0t] Read Addr %0d: %h (OK)", $time, addr, rdata);
            end
        end
    endtask

endmodule