`timescale 1ns/1ps

module tb_mac_engine;

    // 1. Configuration & Parameters (Small for faster simulation)

    parameter int DATA_W    = 16;
    parameter int PRECISION = DATA_W;
    parameter int N_IN      = 4;   // Small for debugging
    parameter int N_HIDDEN  = 8;   
    parameter int P         = 3;   
    
    localparam int ACC_W = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);
 
    // 2. Signal Declarations
    logic clk;
    logic rst_n;
    logic start_compute;
    logic signed [N_IN*DATA_W-1:0] invec_bus;
    logic out_ready;
    
    // DUT Outputs
    logic [$clog2(((N_HIDDEN*N_IN)>1)?(N_HIDDEN*N_IN):2)-1:0] wmem_raddr;
    logic signed [DATA_W-1:0] wmem_rdata;
    logic signed [ACC_W-1:0] out_data;
    logic out_valid;
    logic busy;

    // Test Infrastructure
    logic signed [DATA_W-1:0] input_vec [N_IN];
    logic signed [DATA_W-1:0] weights [N_HIDDEN][N_IN];
    logic signed [ACC_W-1:0]  expected_results [N_HIDDEN];
    logic signed [ACC_W-1:0]  captured_results [N_HIDDEN];
    
    int error_count = 0;
    int test_count = 0;
    int result_idx = 0;


    // 3. DUT Instantiation

    mac_engine #(
        .DATA_W(DATA_W),
        .PRECISION(PRECISION),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .P(P)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .start_compute(start_compute),
        .invec_bus(invec_bus),
        .wmem_raddr(wmem_raddr),
        .wmem_rdata(wmem_rdata),
        .out_data(out_data),
        .out_valid(out_valid),
        .out_ready(out_ready),
        .busy(busy)
    );


    // 4. Clock Generation (100 MHz)

    initial clk = 0;
    always #5 clk = ~clk;


    // 5. Weight Memory Model
 
    always_comb begin
        automatic int h = wmem_raddr / N_IN;
        automatic int i = wmem_raddr % N_IN;
        
        if (h < N_HIDDEN && i < N_IN)
            wmem_rdata = weights[h][i];
        else
            wmem_rdata = '0;
    end


    // 6. Output Capture Monitor

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            result_idx <= 0;
            for (int i = 0; i < N_HIDDEN; i++)
                captured_results[i] <= 'x;
        end else if (out_valid && out_ready) begin
            captured_results[result_idx] <= out_data;
            $display("[%0t] OUTPUT[%0d]: %0d", $time, result_idx, out_data);
            result_idx <= result_idx + 1;
        end
    end

    // 7. Helper Tasks

    
    // Initialize with specific test data
    task setup_data(
        input logic signed [DATA_W-1:0] in_vals[N_IN],
        input logic signed [DATA_W-1:0] wt_vals[N_HIDDEN][N_IN]
    );
        int h, i;
        
        $display("\n[TB] === Setting Up Test Data ===");
        
        // Load input vector
        for (i = 0; i < N_IN; i++) begin
            input_vec[i] = in_vals[i];
            invec_bus[i*DATA_W +: DATA_W] = in_vals[i];
            $display("[TB] Input[%0d] = %0d", i, in_vals[i]);
        end
        
        // Load weights
        for (h = 0; h < N_HIDDEN; h++) begin
            for (i = 0; i < N_IN; i++) begin
                weights[h][i] = wt_vals[h][i];
            end
        end
        
        compute_expected();
        $display("[TB] ================================\n");
    endtask

    // Generate random test data
    task randomize_data();
        int h, i;
        logic signed [DATA_W-1:0] temp_in[N_IN];
        logic signed [DATA_W-1:0] temp_wt[N_HIDDEN][N_IN];
        
        $display("\n[TB] === Randomizing Test Data ===");
        
        for (i = 0; i < N_IN; i++) begin
            temp_in[i] = $random % 200 - 100;
            $display("[TB] Input[%0d] = %0d", i, temp_in[i]);
        end
        
        for (h = 0; h < N_HIDDEN; h++) begin
            for (i = 0; i < N_IN; i++) begin
                temp_wt[h][i] = $random % 100 - 50;
            end
        end
        
        setup_data(temp_in, temp_wt);
    endtask

    // Compute golden reference
    task compute_expected();
        int h, i;
        longint acc;
        
        for (h = 0; h < N_HIDDEN; h++) begin
            acc = 0;
            for (i = 0; i < N_IN; i++) begin
                acc += longint'(input_vec[i]) * longint'(weights[h][i]);
            end
            expected_results[h] = acc[ACC_W-1:0];
            $display("[TB] Expected[%0d] = %0d", h, expected_results[h]);
        end
    endtask

    // Run computation with optional backpressure
    task run_computation(input logic apply_backpressure = 0);
        $display("\n[TB] --- Starting Computation (Backpressure=%0b) ---", apply_backpressure);
        
        // Reset result index and clear captured results
        result_idx = 0;
        for (int i = 0; i < N_HIDDEN; i++)
            captured_results[i] = 'x;
        
        out_ready = 1;
        
        @(posedge clk);
        start_compute = 1;
        @(posedge clk);
        start_compute = 0;
        
        // Wait for busy
        wait(busy);
        $display("[TB] MAC Engine is BUSY at time %0t", $time);
        
        // Apply random backpressure if requested
        if (apply_backpressure) begin
            fork
                begin
                    while (busy || out_valid) begin
                        out_ready = $urandom_range(0, 1);
                        @(posedge clk);
                    end
                    out_ready = 1;
                end
            join_none
        end
        
        // Wait for completion (not busy anymore)
        wait(!busy);
        $display("[TB] MAC Engine returned to IDLE at time %0t", $time);
        
        // Wait for any pending backpressure fork to complete
        if (apply_backpressure) begin
            wait fork;
        end
        
        // Wait a few more cycles to ensure all outputs are captured
        repeat(5) @(posedge clk);
        
        $display("[TB] --- Computation Complete ---\n");
    endtask

    // Verify captured results against golden reference
    task verify_results();
        automatic int errors = 0;
        
        $display("\n[TB] === Verifying Results ===");
        
        if (result_idx != N_HIDDEN) begin
            $error("[TB] ERROR: Got %0d outputs, expected %0d", result_idx, N_HIDDEN);
            errors++;
        end
        
        for (int h = 0; h < N_HIDDEN; h++) begin
            if (captured_results[h] !== expected_results[h]) begin
                $error("[TB] MISMATCH[%0d]: Got %0d, Expected %0d", 
                       h, captured_results[h], expected_results[h]);
                errors++;
            end else begin
                $display("[TB] MATCH[%0d]: %0d", h, captured_results[h]);
            end
        end
        
        if (errors == 0) begin
            $display("[TB] ✓ TEST PASSED");
        end else begin
            $display("[TB] ✗ TEST FAILED: %0d errors", errors);
            error_count += errors;
        end
        
        test_count++;
        $display("[TB] ==============================\n");
    endtask


    // 8. Main Test Sequence

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_mac_engine);
        
        // Initialize signals
        rst_n = 0;
        start_compute = 0;
        out_ready = 1;
        invec_bus = '0;
        result_idx = 0;
        
        // Initialize captured results
        for (int i = 0; i < N_HIDDEN; i++)
            captured_results[i] = 'x;
        
        repeat(3) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        

        // TEST 1: Known values (hand-calculated results)

        begin
           automatic logic signed [DATA_W-1:0] test_in[N_IN] = '{2, 3, -1, 4};
           automatic logic signed [DATA_W-1:0] test_wt[N_HIDDEN][N_IN] = '{
                '{1, 2, 3, 4},     // H0: 2 + 6 - 3 + 16 = 21
                '{-1, -1, -1, -1}, // H1: -2 - 3 + 1 - 4 = -8
                '{5, 0, 0, 0},     // H2: 10
                '{0, 5, 0, 0},     // H3: 15
                '{0, 0, 5, 0},     // H4: -5
                '{0, 0, 0, 5},     // H5: 20
                '{1, 1, 1, 1},     // H6: 8
                '{2, -2, 2, -2}    // H7: 4 - 6 - 2 - 8 = -12
            };
            
            $display("\n╔════════════════════════════════════════════════════════╗");
            $display("║ TEST 1: Known Values (No Backpressure)                ║");
            $display("╚════════════════════════════════════════════════════════╝");
            
            setup_data(test_in, test_wt);
            run_computation(0);
            verify_results();
        end
        

        // TEST 2: Random values

        $display("\n╔════════════════════════════════════════════════════════╗");
        $display("║ TEST 2: Random Values (No Backpressure)               ║");
        $display("╚════════════════════════════════════════════════════════╝");
        
        randomize_data();
        run_computation(0);
        verify_results();
        

        // TEST 3: With AXI backpressure

        $display("\n╔════════════════════════════════════════════════════════╗");
        $display("║ TEST 3: Random Values (WITH Backpressure)             ║");
        $display("╚════════════════════════════════════════════════════════╝");
        
        randomize_data();
        run_computation(1);
        verify_results();

        // TEST 4: All zeros

        begin
            automatic logic signed [DATA_W-1:0] zero_in[N_IN] = '{0, 0, 0, 0};
            automatic logic signed [DATA_W-1:0] any_wt[N_HIDDEN][N_IN] = '{
                '{1, 2, 3, 4},
                '{-1, -1, -1, -1},
                '{5, 0, 0, 0},
                '{0, 5, 0, 0},
                '{0, 0, 5, 0},
                '{0, 0, 0, 5},
                '{1, 1, 1, 1},
                '{2, -2, 2, -2}
            };
            
            $display("\n╔════════════════════════════════════════════════════════╗");
            $display("║ TEST 4: All Zero Inputs                               ║");
            $display("╚════════════════════════════════════════════════════════╝");
            
            setup_data(zero_in, any_wt);
            run_computation(0);
            verify_results();
        end
        

        // TEST 5: Back-to-back computations (accumulator clearing test)

        $display("\n╔════════════════════════════════════════════════════════╗");
        $display("║ TEST 5: Back-to-Back Computations                     ║");
        $display("╚════════════════════════════════════════════════════════╝");
        
        for (int run = 0; run < 2; run++) begin
            $display("\n[TB] --- Run %0d/2 ---", run+1);
            randomize_data();
            run_computation(0);
            verify_results();
        end
        

        // Final Report
 
        repeat(10) @(posedge clk);
        
        $display("\n");
        $display("╔════════════════════════════════════════════════════════╗");
        $display("║               FINAL TEST REPORT                        ║");
        $display("╠════════════════════════════════════════════════════════╣");
        $display("║ Total Tests: %2d                                        ║", test_count);
        $display("║ Total Errors: %2d                                       ║", error_count);
        if (error_count == 0) begin
            $display("║ Status: ✓ ALL TESTS PASSED                            ║");
        end else begin
            $display("║ Status: ✗ SOME TESTS FAILED                           ║");
        end
        $display("╚════════════════════════════════════════════════════════╝");
        $display("\n");
        
        $finish;
    end


    // 9. Real-Time Monitors

    
    // Monitor busy transitions
    always @(posedge clk) begin
        if ($rose(busy)) 
            $display("[%0t] ▶ BUSY ASSERTED", $time);
        if ($fell(busy)) 
            $display("[%0t] ▶ BUSY DE-ASSERTED", $time);
    end
    
    // Monitor state changes
    always @(posedge clk) begin
        if (dut.state != dut.state_n) begin
            case (dut.state_n)
                dut.IDLE:   $display("[%0t] STATE: → IDLE", $time);
                dut.PROC:   $display("[%0t] STATE: → PROC", $time);
                dut.STREAM: $display("[%0t] STATE: → STREAM", $time);
            endcase
        end
    end


    // 10. Assertions for Protocol Checking

    
    // No start_compute when busy
    property p_no_start_when_busy;
        @(posedge clk) disable iff (!rst_n)
        busy |-> !start_compute;
    endproperty
    assert property (p_no_start_when_busy)
        else $error("[%0t] VIOLATION: start_compute asserted while busy!", $time);
    
    // out_valid only in STREAM state or one cycle after (for proper transition)
    property p_valid_only_in_stream;
        @(posedge clk) disable iff (!rst_n)
        out_valid |-> ((dut.state == dut.STREAM) || (dut.state == dut.IDLE && $past(dut.state) == dut.STREAM));
    endproperty
    assert property (p_valid_only_in_stream)
        else $error("[%0t] VIOLATION: out_valid high in unexpected state!", $time);
    
    // Data stable when stalled
    property p_data_stable_when_stalled;
        @(posedge clk) disable iff (!rst_n)
        (out_valid && !out_ready) |=> $stable(out_data);
    endproperty
    assert property (p_data_stable_when_stalled)
        else $error("[%0t] VIOLATION: out_data changed while stalled!", $time);

endmodule