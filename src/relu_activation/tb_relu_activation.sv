`timescale 1ns/1ps

module tb_relu_activation;

   
    // Configuration & Signal Declaration

    parameter int ACC_W = 16; // Using 16 bits for easier readability in logs
                              // (DUT defaults to 64, both work fine)

    logic                     clk;
    logic                     rst_n;
    logic signed [ACC_W-1:0]  in_data;
    logic                     in_valid;
    logic                     out_ready;
    logic signed [ACC_W-1:0]  out_data;
    logic                     out_valid;

    // Simulation control
    int error_count = 0;
    int transaction_count = 0;

    // Queue to act as the "Golden Reference" (Scoreboard)
    logic signed [ACC_W-1:0] expected_queue [$];

    
    // 2. DUT Instantiation
    relu_activation #(
        .ACC_W(ACC_W)
    ) dut (
        .clk      (clk),
        .rst_n    (rst_n),
        .in_data  (in_data),
        .in_valid (in_valid),
        .out_ready(out_ready), 
        .out_data (out_data),
        .out_valid(out_valid)
    );


    // 3. Clock Generation

    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100 MHz)
    end


    // 4. Scoreboard / Monitor (Self-Checking Logic)
    
    // INPUT MONITOR: Capture what goes IN, calculate expected ReLU, push to queue
    // FIXED: Only push when DUT actually accepts the input
    // DUT accepts when: (out_ready || !out_valid) && in_valid
    always @(posedge clk) begin
        if (rst_n && in_valid) begin
            // Check if DUT can accept input (same logic as RTL)
            logic can_accept;
            can_accept = out_ready || !out_valid;
            
            if (can_accept) begin
                logic signed [ACC_W-1:0] expected_val;
                
                // The Golden Logic (ReLU)
                if (in_data < 0) 
                    expected_val = '0;
                else 
                    expected_val = in_data;

                expected_queue.push_back(expected_val);
            end
        end
    end

    // OUTPUT MONITOR: Capture what comes OUT, pop from queue, compare
    // Only pop when handshake completes (out_valid && out_ready)
    always @(posedge clk) begin
        if (rst_n && out_valid && out_ready) begin 
            logic signed [ACC_W-1:0] expected_pop;
            
            if (expected_queue.size() == 0) begin
                $error("[Time %0t] Error: Unexpected output! Queue is empty but out_valid is high.", $time);
                error_count++;
            end else begin
                expected_pop = expected_queue.pop_front();
                
                transaction_count++;
                
                if (out_data !== expected_pop) begin
                    $error("[Time %0t] MISMATCH! Expected: %0d, Got: %0d", $time, expected_pop, out_data);
                    error_count++;
                end else begin
                    // Optional: Uncomment for verbose logging
                    // $display("[Time %0t] OK: Out=%0d", $time, out_data); 
                end
            end
        end
    end


    // 5. Test Stimulus

    initial begin
        // Setup Waveform dumping (viewable in GTKWave or similar)
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_relu_activation);

        $display("---------------------------------------------------");
        $display(" Starting ReLU Activation Testbench ");
        $display("---------------------------------------------------");

        // Initialize inputs
        rst_n     = 0;
        in_valid  = 0;
        in_data   = 0;
        out_ready = 1;  // ADDED: Initialize out_ready (always ready for now)

        // Apply Reset
        repeat(5) @(posedge clk);
        rst_n = 1;
        @(posedge clk);
        $display("Reset released.");

        // --- TEST CASE 1: Basic Corner Cases ---
        $display("\n--- Test Case 1: Corner Cases (0, -1, Max, Min) ---");
        drive_single_input(0);                 // Zero
        drive_single_input(-1);                // Just below zero
        drive_single_input(1);                 // Just above zero
        drive_single_input((1<<(ACC_W-1))-1);  // Max Positive
        drive_single_input(-(1<<(ACC_W-1)));   // Max Negative
        
        // Wait for pipeline to drain
        repeat(5) @(posedge clk);


        // --- TEST CASE 2: Random Values with Gaps ---
        $display("\n--- Test Case 2: Random Inputs with Random Gaps ---");
        repeat(20) begin
            // Randomize data
            logic signed [ACC_W-1:0] rand_data = $urandom();
            
            // Drive data
            drive_single_input(rand_data);
            
            // Insert random bubbles (invalid cycles) 0 to 3 cycles
            repeat($urandom_range(0, 3)) @(posedge clk);
        end
        repeat(5) @(posedge clk); // Drain


        // --- TEST CASE 3: Streaming Burst (Back-to-Back) ---
        $display("\n--- Test Case 3: Streaming Burst (100%% utilization) ---");
        in_valid <= 1'b1;
        repeat(50) begin // Stream 50 items consecutively
            in_data <= $urandom();
            @(posedge clk);
        end
        in_valid <= 1'b0;
        in_data  <= '0;
        
        repeat(10) @(posedge clk); // Drain pipeline


        // --- TEST CASE 4: Backpressure Test ---
        $display("\n--- Test Case 4: Backpressure (out_ready toggling) ---");
        fork
            begin
                // Send 10 values
                repeat(10) begin
                    drive_single_input($urandom());
                    repeat($urandom_range(0, 2)) @(posedge clk);
                end
            end
            begin
                // Randomly assert/deassert out_ready
                repeat(30) begin
                    out_ready <= $urandom_range(0, 1);
                    @(posedge clk);
                end
                out_ready <= 1; // Restore to always ready
            end
        join
        
        repeat(10) @(posedge clk); // Drain


        // End of Simulation

        $display("---------------------------------------------------");
        if (error_count == 0 && expected_queue.size() == 0) begin
            $display(" TEST PASSED! Processed %0d transactions.", transaction_count);
        end else begin
            $display(" TEST FAILED. Errors: %0d, Pending in Queue: %0d", error_count, expected_queue.size());
        end
        $display("---------------------------------------------------");
        
        $finish;
    end

    
    // Helper Task: Drive a single value for one clock cycle

    task drive_single_input(input logic signed [ACC_W-1:0] data);
        begin
            in_data  <= data;
            in_valid <= 1'b1;
            @(posedge clk);
            in_valid <= 1'b0;
            in_data  <= 'x; // Make it obvious in waves if we read invalid data
        end
    endtask

endmodule