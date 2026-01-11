`timescale 1ns/1ps

/**
 * Module: tb_mac_engine
 * Description: Exhaustive testbench for the Bit-Serial MAC Engine.
 *              Validates multi-layer functionality, random data processing, 
 *              and AXI-Stream backpressure resilience.
 */
module tb_mac_engine;


    // 1. Configuration & Parameters (Downscaled for efficient simulation runtime)
    parameter int DATA_W    = 16;       // bit-width of input values
    parameter int PRECISION = DATA_W;   // bit-serial cycles
    parameter int N_IN      = 4;        // input features
    parameter int N_HIDDEN  = 8;        // output hidden neurons
    parameter int N_LAYERS  = 2;        // support for multiple layer contexts
    parameter int P         = 3;        // processing parallelism (lanes)
    
    localparam int ACC_W = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2); // Accumulator width
    localparam int WM_ADDR_W = $clog2(N_LAYERS * N_HIDDEN * N_IN); // Memory address width
    
     
    // 2. Signal Declarations
    logic clk;                  // Testbench clock
    logic rst_n;                // DUT reset
    logic [$clog2(N_LAYERS)-1:0] layer_idx; // Current layer selection
    logic start_compute;        // Trigger to start math
    logic signed [N_IN*DATA_W-1:0] invec_bus; // Parallel input vector
    logic out_ready;            // Downstream ready signal (for handshake test)
    
    // DUT Outputs
    logic [WM_ADDR_W-1:0] wmem_raddr;   // memory address issued by DUT
    logic signed [DATA_W-1:0] wmem_rdata; // memory data returned by TB
    logic signed [ACC_W-1:0] out_data;   // final activation output
    logic out_valid;                     // AXI-Stream valid
    logic busy;                          // Engine status
    logic layer_done;                    // Pulse on layer completion

    // Verification Storage
    logic signed [DATA_W-1:0] input_vec [N_IN];      // Shadow copy of input
    logic signed [DATA_W-1:0] weights [N_LAYERS][N_HIDDEN][N_IN]; // Shadow copy of weights
    logic signed [ACC_W-1:0]  expected_results [N_HIDDEN];        // Golden model results
    logic signed [ACC_W-1:0]  captured_results [N_HIDDEN];        // Actual DUT results
    
    int error_count = 0; // Total mismatches
    int test_count = 0;  // Total test scenarios
    int result_idx = 0;  // Pointer for output capture

   
    // 3. DUT Instantiation
    mac_engine #(
        .DATA_W(DATA_W),
        .PRECISION(PRECISION),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .N_LAYERS(N_LAYERS),
        .P(P)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .layer_idx(layer_idx),
        .start_compute(start_compute),
        .invec_bus(invec_bus),
        .wmem_raddr(wmem_raddr),
        .wmem_rdata(wmem_rdata),
        .out_data(out_data),
        .out_valid(out_valid),
        .out_ready(out_ready),
        .busy(busy),
        .layer_done(layer_done)
    );


    // 4. Clock Generation (100 MHz)
    initial clk = 0;
    always #5 clk = ~clk;

  
    // 5. Weight Memory Behavioral Model
    // Simple combinational model that returns data from our 'weights' array 
    // based on the address issued by the DUT.
    always_comb begin
        automatic int l = wmem_raddr / (N_HIDDEN * N_IN);
        automatic int rem = wmem_raddr % (N_HIDDEN * N_IN);
        automatic int h = rem / N_IN;
        automatic int i = rem % N_IN;
        
        if (l < N_LAYERS && h < N_HIDDEN && i < N_IN)
            wmem_rdata = weights[l][h][i];
        else
            wmem_rdata = '0; // Bound checking protection
    end


    // 6. Output Capture Monitor
    // Listens to the AXI-Stream output and stores results in a local array.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            result_idx <= 0;
            for (int i = 0; i < N_HIDDEN; i++)
                captured_results[i] <= 'x;
        end else if (out_valid && out_ready) begin
            captured_results[result_idx] <= out_data;
            $display("[%0t] MONITOR (OUT): neuron[%0d] = %0d", $time, result_idx, out_data);
            result_idx <= result_idx + 1;
        end
    end


    // 7. Verification Helper Tasks

    // Load static data into the weight bank and input vector
    task setup_data(
        input int cur_l,
        input logic signed [DATA_W-1:0] in_vals[N_IN],
        input logic signed [DATA_W-1:0] wt_vals[N_HIDDEN][N_IN]
    );
        int h, i;
        $display("\n[TB] >>> Configuring Layer %0d with manual values...", cur_l);
        layer_idx = cur_l;

        for (i = 0; i < N_IN; i++) begin
            input_vec[i] = in_vals[i];
            invec_bus[i*DATA_W +: DATA_W] = in_vals[i];
        end
        for (h = 0; h < N_HIDDEN; h++) begin
            for (i = 0; i < N_IN; i++) begin
                weights[cur_l][h][i] = wt_vals[h][i];
            end
        end
        compute_expected(cur_l); // Update golden model
    endtask

    // Randomize weights and inputs for statistical testing
    task randomize_data(input int cur_l);
        logic signed [DATA_W-1:0] temp_in[N_IN];
        logic signed [DATA_W-1:0] temp_wt[N_HIDDEN][N_IN];
        $display("\n[TB] >>> Randomizing values for Layer %0d...", cur_l);
        for (int i = 0; i < N_IN; i++) temp_in[i] = $random;
        for (int h = 0; h < N_HIDDEN; h++)
            for (int i = 0; i < N_IN; i++) temp_wt[h][i] = $random;
        setup_data(cur_l, temp_in, temp_wt);
    endtask

    // Golden Model: Standard software-like matrix-vector multiply
    task compute_expected(input int cur_l);
        longint acc;
        for (int h = 0; h < N_HIDDEN; h++) begin
            acc = 0;
            for (int i = 0; i < N_IN; i++) begin
                acc += longint'(input_vec[i]) * longint'(weights[cur_l][h][i]);
            end
            expected_results[h] = acc[ACC_W-1:0];
        end
    endtask

    // Main control task to trigger the DUT and handle backpressure simulation
    task run_computation(input logic apply_backpressure = 0);
        $display("[TB] --- Initiating Calculation Sequence ---");
        result_idx = 0;
        out_ready = 1;

        @(posedge clk);
        start_compute = 1; // Pulse start
        @(posedge clk);
        start_compute = 0;
        
        wait(busy);
        $display("[TB] DUT Signal: BUSY detected");
        
        if (apply_backpressure) begin
            // Fork a process to toggle 'ready' randomly while data is being streamed out
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
        
        wait(!busy); // Block until FSM returns to IDLE
        $display("[TB] DUT Signal: IDLE detected");
        
        if (apply_backpressure) wait fork;
        repeat(5) @(posedge clk); // Allow final handshake to settle
    endtask

    // Compare captured outputs to golden model
    task verify_results();
        int errors = 0;
        $display("\n[TB] === Verification Results ===");
        if (result_idx != N_HIDDEN) begin
            $error("[FAIL] Missing outputs! Expected %0d, Got %0d", N_HIDDEN, result_idx);
            errors++;
        end
        for (int h = 0; h < N_HIDDEN; h++) begin
            if (captured_results[h] !== expected_results[h]) begin
                $error("[FAIL] Neuron %0d: Expected %d, Got %d", h, expected_results[h], captured_results[h]);
                errors++;
            end
        end
        if (errors == 0) $display("[PASS] All neurons matched the golden reference.");
        error_count += errors;
        test_count++;
    endtask


    // 8. Test Executive Sequence
    initial begin
        // Init signals
        rst_n = 0;
        layer_idx = 0;
        start_compute = 0;
        out_ready = 1;
        invec_bus = '0;

        repeat(5) @(posedge clk);
        rst_n = 1; // Release reset
        repeat(5) @(posedge clk);
        
        // --- Test 1: Deterministic Check ---
        begin
            logic signed [DATA_W-1:0] t_in[4] = '{2, 3, -1, 4};
            logic signed [DATA_W-1:0] t_wt[8][4] = '{
                '{1, 2, 3, 4}, '{1, 1, 1, 1}, '{0, 0, 0, 0}, '{-1, -1, -1, -1},
                '{5, 5, 5, 5}, '{2, 0, 0, 0}, '{0, 2, 0, 0}, '{10, -10, 5, 0}
            };
            setup_data(0, t_in, t_wt);
            run_computation(0);
            verify_results();
        end
        
        // --- Test 2: Random Values Multi-Layer ---
        randomize_data(1);
        run_computation(0);
        verify_results();
        
        // --- Test 3: Stall Stress Test (Backpressure) ---
        randomize_data(0);
        run_computation(1);
        verify_results();
        
        // Final Status Report
        $display("\n");
        $display("**************************************************");
        $display("  MAC ENGINE SIMULATION SUMMARY");
        $display("  Total Tests: %0d", test_count);
        $display("  Final Error Count: %0d", error_count);
        if (error_count == 0) $display("  OVERALL STATUS: SUCCESS");
        else                  $display("  OVERALL STATUS: FAILURE");
        $display("**************************************************");
        $display("\n");
        
        $finish;
    end


    // 9. Protocol Assertions (OVM/UVM Style checking)
    
    // Ensure 'start_compute' is never pulsed while the engine is busy
    assert property (@(posedge clk) disable iff (!rst_n) 
        busy |-> !start_compute) else $error("Protocol Violation: start_compute pulsed during BUSY state.");

    // Ensure out_data remains stable if downstream is NOT ready
    assert property (@(posedge clk) disable iff (!rst_n)
        (out_valid && !out_ready) |=> $stable(out_data)) else $error("Protocol Violation: out_data mutated while stalled.");

endmodule
