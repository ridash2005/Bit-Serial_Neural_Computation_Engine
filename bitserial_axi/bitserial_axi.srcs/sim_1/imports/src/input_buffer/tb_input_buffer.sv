`timescale 1ns/1ps

module tb_input_buffer;


    // 1. Configuration

    parameter int DATA_W = 16;
    parameter int N_IN   = 8;  

    // Signals
    logic clk;
    logic rst_n;
    logic signed [DATA_W-1:0] data_in;
    logic data_in_valid;
    logic vector_last;
    logic busy;
    logic signed [N_IN*DATA_W-1:0] invec_bus;
    logic vector_done;

    // Simulation Stats
    int error_count = 0;
    int vector_count = 0;

    // Golden Reference - Store complete vectors
    logic signed [DATA_W-1:0] current_vector [0:N_IN-1];
    int current_word_idx = 0;
    
    logic signed [DATA_W-1:0] expected_vectors [$][N_IN];


    // 2. DUT Instantiation

    input_buffer #(
        .DATA_W(DATA_W),
        .N_IN  (N_IN)
    ) dut (
        .clk          (clk),
        .rst_n        (rst_n),
        .data_in      (data_in),
        .data_in_valid(data_in_valid),
        .vector_last  (vector_last),
        .busy         (busy),
        .invec_bus    (invec_bus),
        .vector_done  (vector_done)
    );


    // 3. Clock Generation

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end


    // 4. Scoreboard / Monitor


    // INPUT MONITOR - Build complete vectors before comparing
    always @(posedge clk) begin
        if (rst_n && data_in_valid && !busy) begin
            current_vector[current_word_idx] = data_in;
            $display("[Time %0t] INPUT: data=%0d, idx=%0d, vector_last=%0b", 
                     $time, data_in, current_word_idx, vector_last);
            
            // If this completes a vector, save it
            if (vector_last || (current_word_idx == N_IN-1)) begin
                logic signed [DATA_W-1:0] vec_copy [N_IN];
                for (int i = 0; i < N_IN; i++) begin
                    vec_copy[i] = current_vector[i];
                end
                expected_vectors.push_back(vec_copy);
                current_word_idx = 0;
                $display("[Time %0t] >>> Vector captured in golden model", $time);
            end else begin
                current_word_idx++;
            end
        end
    end

    // OUTPUT MONITOR
    always @(posedge clk) begin
        if (rst_n && vector_done) begin
            vector_count++;
            check_output_vector();
        end
    end

    task check_output_vector();
        logic signed [DATA_W-1:0] expected_val;
        logic signed [DATA_W-1:0] actual_val;
        logic signed [DATA_W-1:0] expected_vec [N_IN];
        int i;
        
        $display("[Time %0t] Vector Done triggered. Verifying %0d words...", 
                 $time, N_IN);

        if (expected_vectors.size() == 0) begin
            $error("Error: Vector done, but no expected vector available!");
            error_count++;
            return;
        end

        // Pop the expected vector
        expected_vec = expected_vectors.pop_front();

        for (i = 0; i < N_IN; i++) begin
            expected_val = expected_vec[i];
            actual_val   = invec_bus[(i+1)*DATA_W-1 -: DATA_W];

            if (actual_val !== expected_val) begin
                $error("MISMATCH at index %0d! Exp: %0d, Got: %0d",
                       i, expected_val, actual_val);
                error_count++;
            end
        end
        
        if (error_count == 0 || 
            (vector_count > 1 && error_count == (vector_count - 1) * N_IN)) begin
            $display("          Vector verification passed.");
        end
    endtask


    // 5. Test Stimulus

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_input_buffer);

        rst_n = 0;
        busy = 0;
        data_in_valid = 0;
        data_in = 0;
        vector_last = 0;

        repeat(3) @(posedge clk);
        rst_n = 1;
        @(posedge clk);

        // --- TEST 1 ---
        $display("\n--- Test 1: Simple Sequential Fill ---");
        send_vector_simple();
        repeat(2) @(posedge clk);

        // --- TEST 2 ---
        $display("\n--- Test 2: Fill with Busy Interruptions ---");
        
        // Send 4 words
        repeat(N_IN/2) send_word($urandom_range(1000, 2000));
        
        // Assert busy and try to send a word while busy
        busy = 1;
        $display("[Time %0t] BUSY asserted", $time);
        
        fork
            // Thread 1: Try to send DEAD (will stall until busy=0)
            begin
                send_word(16'hDEAD);
                $display("[Time %0t] DEAD word accepted", $time);
            end
            
            // Thread 2: Release busy after some cycles
            begin
                repeat(5) @(posedge clk);
                busy = 0;
                $display("[Time %0t] BUSY released", $time);
            end
        join
        
        // Send remaining words to complete the vector
        repeat((N_IN/2) - 1) send_word($urandom_range(1000, 2000));
        
        wait_for_vector_done();
        repeat(2) @(posedge clk);

        // --- TEST 3 ---
        $display("\n--- Test 3: Continuous Streaming (3 Vectors) ---");
        repeat(3) begin
            send_vector_streaming();
            wait_for_vector_done();
        end

        // Ensure signals are cleared
        @(negedge clk);
        data_in_valid <= 0;
        vector_last   <= 0;
        repeat(5) @(posedge clk);

        // FINAL REPORT
        $display("\n========================================");
        if (error_count == 0) begin
            $display("TEST PASSED! Vectors processed: %0d", vector_count);
        end else begin
            $display("TEST FAILED. Errors: %0d", error_count);
        end
        $display("Leftover expected vectors: %0d", expected_vectors.size());
        $display("========================================\n");

        $finish;
    end

 
    // Task: Send a complete vector using simple drive

    task send_vector_simple();
        int i;
        for (i = 0; i < N_IN; i++) begin
            send_word($urandom_range(100, 200));
        end
        wait_for_vector_done();
    endtask


    // Task: Send a complete vector using streaming drive

    task send_vector_streaming();
        int i;
        for (i = 0; i < N_IN; i++) begin
            send_word_streaming($urandom(), (i == N_IN-1));
        end
        // Clear signals after last word
        @(negedge clk);
        data_in_valid = 0;
        vector_last = 0;
    endtask


    // Task: Send a single word (waits until accepted, non-blocking = 1 cycle)

    task send_word(input logic signed [DATA_W-1:0] val);
        begin
            // Wait until not busy
            while (busy) @(posedge clk);

            // Drive the data for 1 cycle
            @(negedge clk);  // Drive on negative edge to avoid races
            data_in       = val;
            data_in_valid = 1;
            vector_last   = (current_word_idx == N_IN-1);

            @(posedge clk);  // Wait for positive edge (DUT samples)
            
            // Clear after sampled
            @(negedge clk);
            data_in_valid = 0;
            vector_last   = 0;
        end
    endtask


    // Task: Send word streaming (back-to-back, specify last manually)

    task send_word_streaming(input logic signed [DATA_W-1:0] val, input logic is_last);
        begin
            // Wait until not busy
            while (busy) @(posedge clk);

            // Drive the data
            @(negedge clk);
            data_in       = val;
            data_in_valid = 1;
            vector_last   = is_last;

            @(posedge clk);  // Wait for DUT to sample
            
            // Clear valid if not continuing (but don't clear last yet if it's set)
            // Last will be cleared by the calling task
        end
    endtask


    // Task: Wait for a word to be accepted

    task wait_word_accepted();
        begin
            @(posedge clk);
            while (data_in_valid && busy) @(posedge clk);
        end
    endtask

    // Task: Wait for vector_done pulse

    task wait_for_vector_done();
        begin
            @(posedge clk);
            while (!vector_done) @(posedge clk);
            $display("[Time %0t] >>> Vector done detected", $time);
        end
    endtask

endmodule