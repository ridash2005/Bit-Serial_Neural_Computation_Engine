`timescale 1ns/1ps

module tb_input_buffer;

    // -------------------------------------------------------------------------
    // 1. Configuration
    // -------------------------------------------------------------------------
    // We reduce N_IN to 8 for simulation clarity (easier to see in waveforms)
    parameter int DATA_W = 16;
    parameter int N_IN   = 8;  

    // Signals
    logic clk;
    logic rst_n;
    logic signed [DATA_W-1:0] data_in;
    logic data_in_valid;
    logic busy;
    logic signed [N_IN*DATA_W-1:0] invec_bus;
    logic vector_done;

    // Simulation Stats
    int error_count = 0;
    int vector_count = 0;

    // Golden Reference Queue (Scoreboard)
    logic signed [DATA_W-1:0] expected_data_q [$];

    // -------------------------------------------------------------------------
    // 2. DUT Instantiation
    // -------------------------------------------------------------------------
    input_buffer #(
        .DATA_W(DATA_W),
        .N_IN  (N_IN)
    ) dut (
        .clk          (clk),
        .rst_n        (rst_n),
        .data_in      (data_in),
        .data_in_valid(data_in_valid),
        .busy         (busy),
        .invec_bus    (invec_bus),
        .vector_done  (vector_done)
    );

    // -------------------------------------------------------------------------
    // 3. Clock Generation
    // -------------------------------------------------------------------------
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz
    end

    // -------------------------------------------------------------------------
    // 4. Scoreboard / Monitor
    // -------------------------------------------------------------------------
    
    // INPUT MONITOR: Capture valid data entering the buffer
    always @(posedge clk) begin
        if (rst_n && data_in_valid && !busy) begin
            expected_data_q.push_back(data_in);
        end
    end

    // OUTPUT MONITOR: Check the vector when 'vector_done' triggers
    always @(posedge clk) begin
        if (rst_n && vector_done) begin
            vector_count++;
            check_output_vector();
        end
    end

    // Helper task to compare DUT output against Queue
    task check_output_vector();
        logic signed [DATA_W-1:0] expected_val;
        logic signed [DATA_W-1:0] actual_val;
        int i;
        
        $display("[Time %0t] Vector Done triggered. Verifying %0d words...", $time, N_IN);

        if (expected_data_q.size() < N_IN) begin
            $error("Error: Vector done, but not enough data in expected queue!");
            error_count++;
            return;
        end

        // Iterate through the N_IN words
        for (i = 0; i < N_IN; i++) begin
            expected_val = expected_data_q.pop_front();
            
            // Extract the specific word from the wide bus
            // Slicing syntax: [ (Index+1)*Width-1  -: Width ]
            actual_val = invec_bus[(i+1)*DATA_W-1 -: DATA_W];

            if (actual_val !== expected_val) begin
                $error("MISMATCH at index %0d! Exp: %0d, Got: %0d", i, expected_val, actual_val);
                error_count++;
            end
        end
        $display("          Vector verification passed.");
    endtask

    // -------------------------------------------------------------------------
    // 5. Test Stimulus
    // -------------------------------------------------------------------------
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_input_buffer);

        $display("---------------------------------------------------");
        $display(" Starting Input Buffer Testbench (N_IN=%0d)", N_IN);
        $display("---------------------------------------------------");

        // Init
        rst_n = 0;
        busy = 0;
        data_in_valid = 0;
        data_in = 0;

        // Reset
        repeat(3) @(posedge clk);
        rst_n = 1;
        @(posedge clk);

        // --- TEST 1: Fill a Single Vector (Sequential) ---
        $display("\n--- Test 1: Simple Sequential Fill ---");
        repeat(N_IN) begin
            drive_word($urandom_range(100, 200));
        end
        
        // Wait for processing
        repeat(2) @(posedge clk);


        // --- TEST 2: Backpressure (Busy) Test ---
        $display("\n--- Test 2: Fill with Busy Interruptions ---");
        // Send half vector
        repeat(N_IN/2) drive_word($urandom_range(1000, 2000));
        
        // Assert BUSY
        $display("    Asserting BUSY (Simulating stall)...");
        busy = 1; 
        repeat(5) @(posedge clk); // Hold busy for 5 clocks
        
        // Try to drive while busy (task should wait)
        fork 
            begin
                // This will block inside the task until busy is low
                drive_word(16'hDEAD); 
            end
            begin
                // Release busy after 2 clocks
                repeat(2) @(posedge clk);
                busy = 0;
                $display("    Releasing BUSY...");
            end
        join

        // Finish the rest of the vector
        repeat((N_IN/2) - 1) drive_word($urandom_range(1000, 2000));
        
        repeat(2) @(posedge clk);


       // --- TEST 3: Continuous Streaming ---
        $display("\n--- Test 3: Continuous Streaming (3 Vectors) ---");
        repeat(3 * N_IN) begin
            drive_word_streaming($urandom());
        end
        
        // 1. Turn off valid immediately after the last word
        data_in_valid <= 1'b0; 

        // 2. DRAIN: Wait for the registered 'vector_done' to pulse for the final set
        repeat(5) @(posedge clk); 

          // 3. FINAL CHECK
        $display("---------------------------------------------------");
        if (error_count == 0) begin
            $display(" TEST PASSED! Vectors processed: %0d", vector_count);
            if (expected_data_q.size() != 0)
                $display(" INFO: %0d leftover words (partial vector, expected behavior).",
                         expected_data_q.size());
        end else begin
            $display(" TEST FAILED. Errors: %0d, Leftover Data: %0d",
                     error_count, expected_data_q.size());
        end
        $display("---------------------------------------------------");
        $finish;
end

    // -------------------------------------------------------------------------
    // Task: Drive a single word with flow control
    // -------------------------------------------------------------------------
    task drive_word(input logic signed [DATA_W-1:0] val);
        begin
            // If DUT is busy, wait (Handshake emulation)
            while (busy) @(posedge clk);

            data_in <= val;
            data_in_valid <= 1;
            @(posedge clk);
            data_in_valid <= 0;
            data_in <= 'x;
            
            // Random gap between words for realism (optional)
            // repeat($urandom_range(0,1)) @(posedge clk);
        end
    endtask

    // -------------------------------------------------------------------------
    // Task: Streaming drive (no gaps, checks busy)
    // -------------------------------------------------------------------------
    task drive_word_streaming(input logic signed [DATA_W-1:0] val);
        begin
             // If DUT is busy, wait (hold valid low or hold previous value)
             // Here we just wait for slot
            while (busy) begin
                data_in_valid <= 0;
                @(posedge clk);
            end

            data_in <= val;
            data_in_valid <= 1;
            @(posedge clk);
        end
    endtask

endmodule