`timescale 1ns/1ps

module mac_engine_tb;


    // 1. Configuration & Parameters
    parameter int DATA_W    = 16;
    parameter int PRECISION = DATA_W;
    parameter int N_IN      = 2;  
    parameter int N_HIDDEN  = 8; 
    parameter int P         = 3;  

    
    // 2. Signal Declarations

    logic clk;
    logic rst_n;
    logic start_compute;
    logic signed [N_IN*DATA_W-1:0] invec_bus;
    
    // DUT Outputs
    logic [$clog2(((N_HIDDEN*N_IN)>1)?(N_HIDDEN*N_IN):2)-1:0] wmem_raddr;
    logic signed [DATA_W-1:0] wmem_rdata;
    logic signed [(2*DATA_W)+$clog2((N_IN>1)?N_IN:2)-1:0] out_data;
    logic out_valid;
    logic busy;

    // Internal arrays for Scoreboarding
    logic signed [DATA_W-1:0] input_vec_unpacked [N_IN];
    logic signed [DATA_W-1:0] weights_mem [int];
    logic signed [(2*DATA_W)+$clog2(N_IN)-1:0] expected_results [N_HIDDEN];


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
        .busy(busy)
    );

    
    // 4. Clock & Memory Simulation

    initial clk = 0;
    always #5 clk = ~clk; // 100MHz

    // Memory Model
    always_comb begin
        if (weights_mem.exists(wmem_raddr))
            wmem_rdata = weights_mem[wmem_raddr];
        else
            wmem_rdata = '0;
    end


    // 5. Tasks
    task randomize_data();
        int h, i;
        logic signed [DATA_W-1:0] rand_w;
        
        $display("\n[TB] --- Initializing Memory ---");
        
        // Randomize Inputs
        for (i = 0; i < N_IN; i++) begin
            input_vec_unpacked[i] = $random % 200; 
            invec_bus[i*DATA_W +: DATA_W] = input_vec_unpacked[i];
            $display("[TB] Input[%0d] = %0d", i, input_vec_unpacked[i]);
        end

        // Randomize Weights
        weights_mem.delete();
        for (h = 0; h < N_HIDDEN; h++) begin
            for (i = 0; i < N_IN; i++) begin
                rand_w = $random % 100; 
                weights_mem[(h * N_IN) + i] = rand_w;
                $display("[TB] Weight[H%0d][In%0d] (Addr %0d) = %0d", 
                         h, i, (h * N_IN) + i, rand_w);
            end
        end
        $display("[TB] ---------------------------\n");

        compute_expected();
    endtask

    task compute_expected();
        int h, i;
        longint acc;
        for (h = 0; h < N_HIDDEN; h++) begin
            acc = 0;
            for (i = 0; i < N_IN; i++) begin
                acc += input_vec_unpacked[i] * weights_mem[(h * N_IN) + i];
            end
            expected_results[h] = acc;
        end
    endtask


    // 6. Main Test Sequence 
    initial begin
        rst_n = 0;
        start_compute = 0;
        #20 rst_n = 1;
        #10;

        randomize_data();

        $display("[TB] Starting Simulation...");
        @(posedge clk);
        start_compute = 1;
        @(posedge clk);
        start_compute = 0;

        //  Capture Loop 
        // Instead of just waiting, we loop N_HIDDEN times to catch every neuron
        for (int i = 0; i < N_HIDDEN; i++) begin
            @(posedge clk);
            while (!out_valid) @(posedge clk); // Wait for valid to go high
            $display("[TB] Neuron %0d Output: %d", i, out_data);
            // Optionally compare against your expected software model here
        end

        // Final check to ensure it returns to IDLE
        wait(dut.state == dut.IDLE);
        #100;
        
        $display("\n[TB] --- Final Results ---");
        $display("[TB] Status: Engine returned to IDLE.");
        $finish;
    end


    // 7. REAL-TIME MONITORING (The "Crucial Info")

   /* // Monitor 1: Address Request
    // This confirms the engine is asking for the right data
    always @(posedge clk) begin
        if (dut.mem_read_pending) begin
           $display("[%0t ns] READ_REQ | Addr: %0d | Target Input: %0d | Target Neuron: %0d", 
                    $time, wmem_raddr, dut.cur_input, dut.cur_hidden + dut.mem_lane);
        end
    end
*/

    // Monitor 2: DEEP INSPECTION (Data Path Trace)

    // This block triggers every clock cycle during the processing phase.
    // It prints the internal registers to find where the data becomes 0.
    
   /* always @(posedge clk) begin
        // 1. Check if Weight was loaded correctly
        if (dut.bit_active && dut.bit_idx == 0) begin
             $display("[%0t ns] CHECK    | Input loaded (a_val): %0d", $time, dut.a_val);
             // Loop through parallel lanes
             for (int k=0; k < P; k++) begin
                 $display("                  | Lane %0d Weight (abs_b): %0d (Sign bit: %b)", 
                          k, dut.abs_b[k], dut.sign_prod[k]);
             end
        end

        // 2. Track Partial Sum Accumulation bit-by-bit
        if (dut.bit_active) begin
             $display("[%0t ns] STEP %2d  | Bit: %b | Shifted Input: %6d | Partial Sum: %6d", 
                      $time, 
                      dut.bit_idx, 
                      dut.abs_b[0][dut.bit_idx], // Check bit of weight in Lane 0
                      dut.shifted_abs_a, 
                      dut.partial[0]);           // Check partial accumulator in Lane 0
        end
        
        // 3. Check Final Accumulator Update
        if (dut.bit_active && (dut.bit_idx == PRECISION - 1)) begin
             $display("[%0t ns] UPDATE   | Writing to Hidden Accumulator...", $time);
             $display("                  | Expected Result: -12");
             // Note: The update happens on the NEXT clock edge, so we read the current inputs to the register
             $display("                  | Partial (Final): %0d", dut.partial[0]);
             $display("                  | Sign Logic: %s", dut.sign_prod[0] ? "SUBTRACT" : "ADD");
        end
    end
*/
    // Monitor 3: Busy Signal Check
    always @(posedge clk) begin
        if (start_compute && !busy) 
             $display("[%0t ns] SIGNAL   | Start received. Waiting for BUSY...", $time);
        if ($rose(busy)) 
             $display("[%0t ns] SIGNAL   | BUSY asserted (High). Engine Running.", $time);
        if ($fell(busy)) 
             $display("[%0t ns] SIGNAL   | BUSY de-asserted (Low). Processing Complete.", $time);
    end

    // Monitor 4: Output Output
    always @(posedge clk) begin
        if (out_valid) begin
             $display("[%0t ns] OUTPUT   | Result Valid! Data: %0d", $time, out_data);
        end
    end

endmodule