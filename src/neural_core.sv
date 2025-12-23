`timescale 1ns/1ps

module neural_core;

    // =========================================================================
    // 1. Parameters & Configuration
    // =========================================================================
    // We use smaller dimensions than the default to make the simulation 
    // run faster and easier to debug, but the logic remains the same.
    parameter int DATA_W    = 8;
    parameter int N_IN      = 8;   // Input vector size
    parameter int N_HIDDEN  = 4;   // Number of neurons (outputs)
    parameter int P         = 2;   // Parallelism factor (PEs)
    
    // Calculate the Accumulator width exactly as the MAC engine does
    // so we can pass it correctly to the ReLU module.
    localparam int IN_CNT_W = $clog2((N_IN>1)?N_IN:2);
    localparam int MAC_ACC_W = (2*DATA_W) + IN_CNT_W;

    // =========================================================================
    // 2. Signals
    // =========================================================================
    logic clk;
    logic rst_n;
    logic start_compute;
    logic busy;

    // Input Bus (Packed Vector)
    logic signed [N_IN*DATA_W-1:0] invec_bus;

    // Memory Interface (MAC <-> TB Memory)
    logic [$clog2(N_HIDDEN*N_IN)-1:0] wmem_raddr;
    logic signed [DATA_W-1:0]         wmem_rdata;

    // Interconnect (MAC -> ReLU)
    logic signed [MAC_ACC_W-1:0] mac_out_data;
    logic                        mac_out_valid;

    // Output (ReLU -> TB Checker)
    logic signed [MAC_ACC_W-1:0] relu_out_data;
    logic                        relu_out_valid;

    // Testbench Storage
    logic signed [DATA_W-1:0] tb_inputs  [N_IN];
    logic signed [DATA_W-1:0] tb_weights [N_HIDDEN * N_IN];
    logic signed [MAC_ACC_W-1:0] expected_queue [$]; // Queue for expected results

    // =========================================================================
    // 3. DUT Instances
    // =========================================================================

    // Instance 1: The MAC Engine
    mac_engine #(
        .DATA_W(DATA_W),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .P(P)
    ) dut_mac (
        .clk(clk),
        .rst_n(rst_n),
        .start_compute(start_compute),
        .invec_bus(invec_bus),
        .wmem_raddr(wmem_raddr),
        .wmem_rdata(wmem_rdata),
        .out_data(mac_out_data),
        .out_valid(mac_out_valid),
        .busy(busy)
    );

    // Instance 2: The ReLU Activation
    // Note: We map the MAC output width to the ReLU ACC_W parameter
    relu_activation #(
        .ACC_W(MAC_ACC_W)
    ) dut_relu (
        .clk(clk),
        .rst_n(rst_n),
        .in_data(mac_out_data),
        .in_valid(mac_out_valid),
        .out_data(relu_out_data),
        .out_valid(relu_out_valid)
    );

    // =========================================================================
    // 4. Clock & Reset Generation
    // =========================================================================
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end

    // =========================================================================
    // 5. Memory Simulation (Mock Weight RAM)
    // =========================================================================
    // The MAC engine expects 1 cycle latency. 
    // Address valid at T0 -> Data valid at T1 (ready for capture at T2 edge)
    always_ff @(posedge clk) begin
        wmem_rdata <= tb_weights[wmem_raddr];
    end

    // =========================================================================
    // 6. Test Stimulus & Golden Model
    // =========================================================================
    initial begin
        // --- Initialization ---
        rst_n = 0;
        start_compute = 0;
        invec_bus = '0;
        expected_queue = {};
        
        // Randomize Weights
        $display("--- Initializing Memory ---");
        for (int i = 0; i < N_HIDDEN * N_IN; i++) begin
            tb_weights[i] = $random; // Random 8-bit signed
        end

        // Wait for reset
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);

        // --- Run Multiple Test Cases ---
        run_test_case(1); // Run 1
        repeat(20) @(posedge clk); // Gap
        run_test_case(2); // Run 2
        
        repeat(50) @(posedge clk);
        $display("--- Simulation Finished Successfully ---");
        $finish;
    end

    // Task to execute a full inference cycle
    task run_test_case(int test_id);
        longint sum;
        longint relu_res;
        
        $display("\nStarting Test Case %0d...", test_id);

        // 1. Generate Input Vector
        for (int i = 0; i < N_IN; i++) begin
            tb_inputs[i] = $random;
            // Pack into the flat bus (Little Endian packing)
            invec_bus[i*DATA_W +: DATA_W] = tb_inputs[i];
        end

        // 2. Compute Expected Golden Results (Software Model)
        // Matrix Multiplication: Output[h] = Sum(Input[i] * Weight[h][i])
        for (int h = 0; h < N_HIDDEN; h++) begin
            sum = 0;
            for (int i = 0; i < N_IN; i++) begin
                // Note: The MAC address logic is (h * N_IN) + i
                sum = sum + (tb_inputs[i] * tb_weights[h*N_IN + i]);
            end
            
            // Apply ReLU
            if (sum < 0) relu_res = 0;
            else relu_res = sum;
            
            expected_queue.push_back(relu_res);
            $display("Golden Model [%0d]: MVM=%0d, ReLU=%0d", h, sum, relu_res);
        end

        // 3. Start Hardware Engine
        @(posedge clk);
        start_compute <= 1;
        @(posedge clk);
        start_compute <= 0;

        // 4. Wait for hardware to finish
        wait(busy == 1);
        wait(busy == 0);
        
        // Wait a few extra cycles for the ReLU pipeline flush
        repeat(5) @(posedge clk);

        // 5. Check if we received all data
        if (expected_queue.size() != 0) begin
            $error("Error: Not all expected data was received! Remaining items: %0d", expected_queue.size());
        end else begin
            $display("Test Case %0d PASSED", test_id);
        end
    endtask

    // =========================================================================
    // 7. Output Monitor / Scoreboard
    // =========================================================================
    always_ff @(posedge clk) begin
        if (relu_out_valid) begin
            logic signed [MAC_ACC_W-1:0] expected_val;
            
            if (expected_queue.size() == 0) begin
                $error("Error: Received unexpected valid data from DUT!");
            end else begin
                expected_val = expected_queue.pop_front();
                
                if (relu_out_data !== expected_val) begin
                    $error("MISMATCH! Time: %0t | Expected: %0d | Got: %0d", 
                           $time, expected_val, relu_out_data);
                end else begin
                    $display("Match! Time: %0t | Output: %0d", $time, relu_out_data);
                end
            end
        end
    end

endmodule