`timescale 1ns/1ps

/**
 * Module: tb_input_buffer
 * Description: Testbench for the input_buffer module.
 *              Includes a golden model (scoreboard) that pushes expected vectors
 *              to a queue and verifies them against the DUT output bus.
 */
module tb_input_buffer;


    // 1. Configuration Parameters
    parameter int DATA_W = 16;  // Element bit-width
    parameter int N_IN   = 8;   // Reduction scale for faster simulation

    // Signal Declarations
    logic clk;                  // Testbench clock
    logic rst_n;                // DUT reset
    logic signed [DATA_W-1:0] data_in;       // Source data stream
    logic data_in_valid;                     // Source valid signal
    logic vector_last;                       // Source TLAST (end of vector)
    logic busy;                              // Downstream backpressure (controlled by TB)
    logic signed [N_IN*DATA_W-1:0] invec_bus; // DUT output bus (Parallel)
    logic vector_done;                       // DUT output pulse (Vector ready)

    // Simulation Monitoring Variables
    int error_count = 0;        // Track mismatches
    int vector_count = 0;       // Track successful transfers

    // Golden Reference Model Infrastructure
    // Temporary storage for words as they arrive at the input
    logic signed [DATA_W-1:0] current_vector [0:N_IN-1];
    int current_word_idx = 0;
    
    // Scoreboard Queue: Stores whole vectors expected at the output
    logic signed [DATA_W-1:0] expected_vectors [$][N_IN];


    // 2. DUT (Device Under Test) Instantiation
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


    // 3. Clock Generation (100 MHz)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end


    // 4. Scoreboard / Monitor Logic

    /**
     * INPUT MONITOR (Golden Model):
     * Watches the input pins and builds a local 'expected' copy of the vector.
     * Only samples when (!busy && data_in_valid) to mirror DUT behavior.
     */
    always @(posedge clk) begin
        if (rst_n && data_in_valid && !busy) begin
            // Store the incoming word in the local shadow array
            current_vector[current_word_idx] = data_in;
            $display("[Time %0t] MONITOR (IN): data=%0d, idx=%0d, last=%0b", 
                     $time, data_in, current_word_idx, vector_last);
            
            // Check if this word completes a vector
            if (vector_last || (current_word_idx == N_IN-1)) begin
                // Push the complete vector to the expected queue for later checking
                logic signed [DATA_W-1:0] vec_copy [N_IN];
                for (int i = 0; i < N_IN; i++) begin
                    vec_copy[i] = current_vector[i];
                end
                expected_vectors.push_back(vec_copy);
                current_word_idx = 0; // Reset for next vector
                $display("[Time %0t] >>> Scoreboard: Vector queued for validation", $time);
            end else begin
                current_word_idx++;
            end
        end
    end

    /**
     * OUTPUT MONITOR:
     * Triggers whenever the DUT asserts 'vector_done' to compare the 
     * parallel 'invec_bus' against the scoreboard.
     */
    always @(posedge clk) begin
        if (rst_n && vector_done) begin
            vector_count++;
            check_output_vector();
        end
    end

    // Task to compare DUT output against scoreboard
    task check_output_vector();
        logic signed [DATA_W-1:0] expected_val;
        logic signed [DATA_W-1:0] actual_val;
        logic signed [DATA_W-1:0] expected_vec [N_IN];
        int i;
        
        $display("[Time %0t] Verifying vector #%0d...", $time, vector_count);

        if (expected_vectors.size() == 0) begin
            $error("[FAIL] Error: DUT signaled vector_done but scoreboard is empty!");
            error_count++;
            return;
        end

        // Pop the oldest expected vector from the queue
        expected_vec = expected_vectors.pop_front();

        // Check word-by-word (parallel slice by parallel slice)
        for (i = 0; i < N_IN; i++) begin
            expected_val = expected_vec[i];
            actual_val   = invec_bus[(i+1)*DATA_W-1 -: DATA_W];

            if (actual_val !== expected_val) begin
                $error("[FAIL] Index %0d: Expected %d, Got %d", i, expected_val, actual_val);
                error_count++;
            end
        end
        
        if (error_count == 0) begin
            $display("          [PASS] Vector matches golden model perfectly.");
        end
    endtask


    // 5. Test Stimulus Sequence

    initial begin
        // Waveform captures
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_input_buffer);

        // Initialize signals to safe defaults
        rst_n = 0;
        busy = 0;
        data_in_valid = 0;
        data_in = 0;
        vector_last = 0;

        // Reset Sequence
        repeat(3) @(posedge clk);
        rst_n = 1;
        @(posedge clk);

        // --- TEST 1: Simple Sequential Fill ---
        $display("\n--- TEST 1: Basic Linear Vector Fill ---");
        send_vector_simple();
        repeat(5) @(posedge clk);

        // --- TEST 2: Fill with Backpressure (Downstream Busy) ---
        $display("\n--- TEST 2: Testing Stall Durations (Busy) ---");
        
        // Send half words
        repeat(N_IN/2) send_word($urandom_range(1000, 2000));
        
        // Assert busy (stalling the DUT)
        busy = 1;
        $display("[Time %0t] Downstream BUSY triggered", $time);
        
        fork
            // Thread A: Try to send fresh data (should wait for busy=0 internally)
            begin
                send_word(16'hDEAD);
                $display("[Time %0t] Stalled word (DEAD) successfully accepted", $time);
            end
            
            // Thread B: Wait a few cycles then release busy
            begin
                repeat(10) @(posedge clk);
                busy = 0;
                $display("[Time %0t] Downstream BUSY released", $time);
            end
        join
        
        // Complete the vector
        repeat((N_IN/2) - 1) send_word($urandom_range(1000, 2000));
        
        wait_for_vector_done();
        repeat(5) @(posedge clk);

        // --- TEST 3: Continuous Burst Streaming ---
        $display("\n--- TEST 3: Bursting 3 Vectors Back-to-Back ---");
        repeat(3) begin
            send_vector_streaming();
            wait_for_vector_done();
        end

        // Final Verification Summary
        $display("\n========================================");
        if (error_count == 0) begin
            $display("  OVERALL STATUS: SUCCESS");
            $display("  Vectors Verified: %0d", vector_count);
        end else begin
            $display("  OVERALL STATUS: FAILED");
            $display("  Total Errors: %0d", error_count);
        end
        $display("========================================\n");

        $finish;
    end

 
    // HELPER TASKS for Stimulus Generation

    // Drive a vector with standard non-bursting logic
    task send_vector_simple();
        int i;
        for (i = 0; i < N_IN; i++) begin
            send_word($signed(i + 10));
        end
        wait_for_vector_done();
    endtask

    // Drive a vector using back-to-back streaming cycles
    task send_vector_streaming();
        int i;
        for (i = 0; i < N_IN; i++) begin
            send_word_streaming($signed($random), (i == N_IN-1));
        end
        // Reset valid bit immediately after last word to avoid trailing writes
        @(negedge clk);
        data_in_valid = 0;
        vector_last = 0;
    endtask

    // Send a single word with handshake handling
    task send_word(input logic signed [DATA_W-1:0] val);
        begin
            // Block while the DUT/Downstream is busy
            while (busy) @(posedge clk);

            // Synchronize to negative edge to cleanly drive data before positive edge
            @(negedge clk);
            data_in       = val;
            data_in_valid = 1;
            vector_last   = (current_word_idx == N_IN-1);

            @(posedge clk); // DUT samples here
            
            // Clear signals after transfer
            @(negedge clk);
            data_in_valid = 0;
            vector_last   = 0;
        end
    endtask

    // Send word without clearing 'valid' between cycles (Bursting)
    task send_word_streaming(input logic signed [DATA_W-1:0] val, input logic is_last);
        begin
            while (busy) @(posedge clk);

            @(negedge clk);
            data_in       = val;
            data_in_valid = 1;
            vector_last   = is_last;

            @(posedge clk); // DUT samples
        end
    endtask

    // Wait for the DUT to pulse vector_done
    task wait_for_vector_done();
        begin
            @(posedge clk);
            while (!vector_done) @(posedge clk);
            $display("[Time %0t] >>> VECTOR_DONE Pulse Captured", $time);
        end
    endtask

endmodule
