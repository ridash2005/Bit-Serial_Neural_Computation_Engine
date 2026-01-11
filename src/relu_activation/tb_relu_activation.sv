`timescale 1ns/1ps

/**
 * Module: tb_relu_activation
 * Description: Testbench for the ReLU activation module.
 *              Employs an AXI-Stream bus monitor and scoreboard to verify 
 *              clipping logic and backpressure stability.
 */
module tb_relu_activation;

   
    // 1. Configuration & Signal Declaration
    parameter int ACC_W = 16;   // Small bit-width for trace readability

    logic                     clk;       // master clock
    logic                     rst_n;     // chip reset
    logic signed [ACC_W-1:0]  in_data;   // source data
    logic                     in_valid;  // source valid
    logic                     out_ready; // destination ready (backpressure)
    logic signed [ACC_W-1:0]  out_data;  // DUT activation output
    logic                     out_valid; // DUT valid strobe

    // Simulation Stats
    int error_count = 0;
    int transaction_count = 0;

    /**
     * Golden Reference (Scoreboard Queue)
     * Every valid input accepted by the DUT is transformed by the ReLU 
     * function and stored in this queue to be compared against the DUT output.
     */
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


    // 3. Clock Generation (100 MHz)
    initial begin
        clk = 0;
        forever #5 clk = ~clk; 
    end


    // 4. Scoreboard / Monitor Logic (Self-Checking)
    
    /**
     * INPUT MONITOR:
     * Samples the input bus on every clock edge. If (valid && ready), 
     * it calculates the MIN(0, x) and stores it as the 'expected' result.
     */
    always @(posedge clk) begin
        if (rst_n && in_valid) begin
            // Manual handshake calculation mirroring RTL behavior (skid buffer logic)
            logic can_accept;
            can_accept = out_ready || !out_valid;
            
            if (can_accept) begin
                logic signed [ACC_W-1:0] expected_val;
                
                // ReLU Golden Logic: Clip negatives to zero
                if (in_data < 0) 
                    expected_val = '0;
                else 
                    expected_val = in_data;

                expected_queue.push_back(expected_val);
            end
        end
    end

    /**
     * OUTPUT MONITOR:
     * Verifies every word that leaves the Master AXI-Stream interface.
     */
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            transaction_count <= 0;
            error_count <= 0;
        end else if (out_valid && out_ready) begin 
            logic signed [ACC_W-1:0] expected_pop;
            
            if (expected_queue.size() == 0) begin
                $error("[FAIL] Unexpected output: Queue is empty but out_valid is high!");
                error_count++;
            end else begin
                // Pull from head of scoreboard queue
                expected_pop = expected_queue.pop_front();
                transaction_count++;
                
                // Comparison check
                if (out_data !== expected_pop) begin
                    $error("[FAIL] Word %0d Mismatch: Exp=%d, Got=%d", transaction_count, expected_pop, out_data);
                    error_count++;
                end
            end
        end
    end


    // 5. Test Stimulus Executive Sequence

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_relu_activation);

        $display("\n---------------------------------------------------");
        $display("   ReLU ACTIVATION MODULE VERIFICATION   ");
        $display("---------------------------------------------------\n");

        // Init signals
        rst_n     = 0;
        in_valid  = 0;
        in_data   = 0;
        out_ready = 1; 

        repeat(5) @(posedge clk);
        rst_n = 1; // Release reset
        @(posedge clk);

        // --- TEST 1: Edge Cases (0, -1, Max, Min) ---
        $display("[TEST 1] Feeding critical edge cases...");
        drive_single_input(0);                 
        drive_single_input(-1);                
        drive_single_input(1);                 
        drive_single_input((1<<(ACC_W-1))-1);  // Max +
        drive_single_input(-(1<<(ACC_W-1)));   // Max -
        
        repeat(5) @(posedge clk); // Pipeline drain


        // --- TEST 2: Random Values with Intervals ---
        $display("[TEST 2] Random inputs with variable gaps...");
         repeat(50) begin
             drive_single_input($random % 500); 
             // Random stall between words
             repeat($urandom_range(0, 3)) @(posedge clk);
         end
        repeat(5) @(posedge clk);


        // --- TEST 3: Full-Throttle Streaming ---
        $display("[TEST 3] 100%% throughput burst test...");
        in_valid <= 1'b1;
        repeat(100) begin
            in_data <= $random;
            @(posedge clk);
        end
        in_valid <= 1'b0;
        repeat(5) @(posedge clk);


        // --- TEST 4: Backpressure Stress ---
        $display("[TEST 4] Downstream Backpressure Stress-Test...");
        fork
            // Thread A: Rapidly push data
            begin
                repeat(20) begin
                    drive_single_input($random);
                    repeat($urandom_range(0, 2)) @(posedge clk);
                end
            end
            // Thread B: Rapidly toggle out_ready (stalling the DUT randomly)
            begin
                repeat(40) begin
                    out_ready <= $urandom_range(0, 1);
                    @(posedge clk);
                end
                out_ready <= 1; // restore
            end
        join
        
        repeat(10) @(posedge clk);


        // Final Result Log
        $display("\n---------------------------------------------------");
        if (error_count == 0 && expected_queue.size() == 0) begin
            $display("   STATUS: SUCCESS");
            $display("   Successful Handshakes: %0d", transaction_count);
        end else begin
            $display("   STATUS: FAILED");
            $display("   Errors: %0d | In-flight words: %0d", error_count, expected_queue.size());
        end
        $display("---------------------------------------------------\n");
        
        $finish;
    end

    
    // TASK: drive_single_input
    // Encapsulates a one-cycle valid data transfer
    task drive_single_input(input logic signed [ACC_W-1:0] data);
        begin
            in_data  <= data;
            in_valid <= 1'b1;
            @(posedge clk);
            in_valid <= 1'b0;
            in_data  <= 'x; 
        end
    endtask

endmodule

