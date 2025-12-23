`timescale 1ns/1ps

module tb_wmem_hidden;

    // ---------------------------------------------------------
    // 1. Parameters & Signals
    // ---------------------------------------------------------
    parameter int DATA_W   = 16;
    parameter int N_IN     = 8;  
    parameter int N_HIDDEN = 4;
    
    localparam int WMEM_SIZE = N_HIDDEN * N_IN;
    localparam int ADDR_H_W  = $clog2(N_HIDDEN);
    localparam int ADDR_I_W  = $clog2(N_IN);
    localparam int RADDR_W   = $clog2(WMEM_SIZE);

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

    // ---------------------------------------------------------
    // 2. DUT Instantiation
    // ---------------------------------------------------------
    wmem_hidden #(
        .DATA_W(DATA_W),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN)
    ) dut (.*);

    // ---------------------------------------------------------
    // 3. Clock Generation
    // ---------------------------------------------------------
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100 MHz
    end

    // ---------------------------------------------------------
    // 4. Test Stimulus
    // ---------------------------------------------------------
    initial begin
        $dumpfile("wmem_dump.vcd");
        $dumpvars(0, tb_wmem_hidden);

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
        w_wr_en <= 0; // Stop writing

        // CRITICAL: The DUT has a 1-cycle data pipeline (w_data_pipe).
        // We must wait for the last write to actually propagate into the BRAM array
        // before we attempt to read it back.
        repeat(2) @(posedge clk);

        // --- TEST 2: Verify Read Latency and Data ---
        $display("--- Test 2: Verifying Reads ---");
        for (int addr = 0; addr < WMEM_SIZE; addr++) begin
            check_read(addr);
        end

        // --- TEST 3: Random Access Write/Read ---
        $display("--- Test 3: Random Access ---");
        repeat(15) begin
            // Explicitly automatic to ensure local scope in loop iterations
            automatic int rh   = $urandom_range(0, N_HIDDEN-1);
            automatic int ri   = $urandom_range(0, N_IN-1);
            automatic int rval = $urandom_range(-500, 500);
            
            write_weight(rh, ri, $signed(rval));
            
            // Allow pipeline to settle
            repeat(2) @(posedge clk);
            
            check_read(rh * N_IN + ri);
        end

        $display("\nAll simulations complete. Total Errors: %0d", error_count); // Assuming error_count logic added or just check logs
        $finish;
    end

    // ---------------------------------------------------------
    // Helper Tasks (Declared Automatic)
    // ---------------------------------------------------------
   

    // Corrected to handle the piped data write
    task automatic write_weight(
        input [ADDR_H_W-1:0] h, 
        input [ADDR_I_W-1:0] i, 
        input signed [DATA_W-1:0] data
    );
        begin
            w_addr_h <= h;
            w_addr_i <= i;
            w_data   <= data; 
            w_wr_en  <= 1;
            
            // Update shadow memory: 
            // We store 'data' because even though it's delayed in the DUT, 
            // it will eventually reach this address.
            shadow_mem[h * N_IN + i] = data;

            @(posedge clk);
            w_wr_en <= 0; // Pulse write enable
        end
    endtask

    // Corrected for Synchronous BRAM Read (1-cycle delay)
    task automatic check_read(input [RADDR_W-1:0] addr);
        logic signed [DATA_W-1:0] expected;
        begin
            raddr <= addr;      // Set address
            expected = shadow_mem[addr];
            
            @(posedge clk);     // BRAM Latency: Wait 1 cycle for rdata to update
            #1;                 // Small offset to sample values after the clock edge
            
            if (rdata !== expected) begin
                $error("[Time %0t] Read Mismatch at Addr %0d! Exp: %h, Got: %h", 
                        $time, addr, expected, rdata);
                error_count++;
            end else begin
                $display("[Time %0t] Read Addr %0d: %h (OK)", $time, addr, rdata);
            end
        end
    endtask

endmodule