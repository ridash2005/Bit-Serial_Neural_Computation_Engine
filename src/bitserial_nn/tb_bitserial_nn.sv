`timescale 1ns/1ps

/**
 * Module: tb_bitserial_nn
 * Description: System-level testbench for the Multi-Layer Bit-Serial Engine.
 *              Validates end-to-end inference from Layer 0 input features 
 *              to the final Master AXI-Stream output activations.
 */
module tb_bitserial_nn;

    // 1. Configuration Parameters (Scaled for verification visibility)
    localparam int DATA_W    = 16;
    localparam int PRECISION = 16;
    localparam int N_IN      = 4;   // Input features
    localparam int N_HIDDEN  = 8;   // Hidden neurons
    localparam int N_LAYERS  = 3;   // Number of layers to process
    localparam int P         = 1;   // Parallel processing factor

    localparam int ACC_W = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);

    // 2. Signal Declarations
    logic clk;
    logic rst_n;

    // Slave AXI-Stream (Input side)
    logic [DATA_W-1:0] s_axis_tdata;
    logic              s_axis_tvalid;
    logic              s_axis_tready;
    logic              s_axis_tlast;

    // Master AXI-Stream (Output side)
    logic [DATA_W-1:0] m_axis_tdata;
    logic              m_axis_tvalid;
    logic              m_axis_tready;
    logic              m_axis_tlast;

    // Weight Load Interface
    logic                                        w_wr_en;
    logic [$clog2((N_LAYERS > 1) ? N_LAYERS : 2)-1:0]  w_addr_l;
    logic [$clog2((N_HIDDEN > 1) ? N_HIDDEN : 2)-1:0]  w_addr_h;
    logic [$clog2((N_IN > 1) ? N_IN : 2)-1:0]          w_addr_i;
    logic signed [DATA_W-1:0]                   w_data;

    // DUT status
    logic busy;


    // 3. DUT Instantiation
    bitserial_nn #(
        .DATA_W(DATA_W),
        .PRECISION(PRECISION),
        .N_IN(N_IN),
        .N_HIDDEN(N_HIDDEN),
        .N_LAYERS(N_LAYERS),
        .P(P)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .w_wr_en(w_wr_en),
        .w_addr_l(w_addr_l),
        .w_addr_h(w_addr_h),
        .w_addr_i(w_addr_i),
        .w_data(w_data),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast)
    );


    // 4. Clock Generation (100 MHz)
    initial clk = 0;
    always #5 clk = ~clk;


    // 5. Verification Storage (Golden Reference Model)
    logic signed [DATA_W-1:0] golden_weights [N_LAYERS][N_HIDDEN][N_IN];
    logic signed [DATA_W-1:0] layer_results [N_LAYERS+1][N_HIDDEN];

    // Total test stats
    int error_count = 0;
    int items_received = 0;


    // 6. Test Stimulus Executive Tasks

    /**
     * Task: load_weights
     * Populates the internal weight memory of the DUT with random but deterministic values.
     */
    task load_weights();
        $display("[TB] >>> Starting Weight Loading Protocol...");
        w_wr_en = 0;
        for (int l = 0; l < N_LAYERS; l++) begin
            for (int h = 0; h < N_HIDDEN; h++) begin
                for (int i = 0; i < N_IN; i++) begin
                    @(posedge clk);
                    w_wr_en  = 1;
                    w_addr_l = l;
                    w_addr_h = h;
                    w_addr_i = i;
                    // Simple deterministic weights: (layer+1)*10 + neuron + input
                    w_data   = $signed((l+1)*10 + h + i); 
                    golden_weights[l][h][i] = w_data;
                end
            end
        end
        @(posedge clk);
        w_wr_en = 0;
    endtask


    /**
     * Task: compute_golden
     * Software-side matrix emulation to calculate expected activations.
     */
    task compute_golden(input logic signed [DATA_W-1:0] features[N_IN]);
        longint acc;
        $display("[TB] >>> Calculating Golden Model for %0d Layers...", N_LAYERS);
        
        // Setup initial Layer 0 input
        for (int i = 0; i < N_IN; i++) layer_results[0][i] = features[i];

        for (int l = 0; l < N_LAYERS; l++) begin
            for (int h = 0; h < N_HIDDEN; h++) begin
                acc = 0;
                for (int i = 0; i < N_IN; i++) begin
                    // Note: If N_IN > N_HIDDEN of previous layer, we zero-pad the input
                    logic signed [DATA_W-1:0] in_val;
                    in_val = (i < N_HIDDEN || l == 0) ? layer_results[l][i] : '0;
                    acc += longint'(in_val) * longint'(golden_weights[l][h][i]);
                end
                // ReLU + Truncation to match hardware bit-depth recycling
                layer_results[l+1][h] = (acc < 0) ? '0 : acc[DATA_W-1:0];
            end
        end
    endtask


    /**
     * Task: push_input_vector
     * Drives a full input feature vector into the s_axis interface.
     */
    task push_input_vector(input logic signed [DATA_W-1:0] features[N_IN]);
        $display("[TB] >>> Pushing Input Stream to AXI Slave...");
        for (int i = 0; i < N_IN; i++) begin
            s_axis_tdata  = features[i];
            s_axis_tlast  = (i == N_IN-1);
            s_axis_tvalid = 1;
            
            // Wait for slave to acknowledge (standard AXI handshake)
            do @(posedge clk);
            while (!(s_axis_tvalid && s_axis_tready));
            
            s_axis_tvalid = 0;
            s_axis_tlast  = 0;
        end
    endtask


    // 7. Main Sequence Execution
    initial begin
        // Reset and Waveform setup
        $dumpfile("bitserial_nn.vcd");
        $dumpvars(0, tb_bitserial_nn);
        
        rst_n         = 0;
        s_axis_tvalid = 0;
        m_axis_tready = 1; // Master is always ready to sink data
        w_wr_en       = 0;

        repeat(10) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);

        // Pre-compute cycle
        begin
            logic signed [DATA_W-1:0] test_vector [N_IN];
            for (int k=0; k<N_IN; k++) test_vector[k] = $signed(k + 1);

            load_weights();
            compute_golden(test_vector);
            push_input_vector(test_vector);
        end

        // Monitor and Collect Outputs
        $display("[TB] >>> Monitoring Master Output Stream...");
        items_received = 0;
        while (items_received < N_HIDDEN) begin
            @(posedge clk);
            if (m_axis_tvalid && m_axis_tready) begin
                $display("[WORD %0d] Master Data: %d | Expected: %d | tlast: %b", 
                         items_received, m_axis_tdata, layer_results[N_LAYERS][items_received], m_axis_tlast);
                
                if (m_axis_tdata !== layer_results[N_LAYERS][items_received]) begin
                    $error("[FAIL] Data Mismatch at index %0d!", items_received);
                    error_count++;
                end
                
                if (items_received == N_HIDDEN-1 && !m_axis_tlast) begin
                    $error("[FAIL] Protocol Violation: m_axis_tlast not asserted on last word.");
                    error_count++;
                end

                items_received++;
            end
        end

        // Final Report
        $display("\n=======================================================");
        $display("   SYSTEM INTEGRATION VERIFICATION COMPLETE");
        $display("   Total Items Verified: %0d", items_received);
        if (error_count == 0) begin
            $display("   OVERALL RESULT: SUCCESS (All layers matched)");
        end else begin
            $display("   OVERALL RESULT: FAILED (%0d mismatches found)", error_count);
        end
        $display("=======================================================\n");

        repeat(20) @(posedge clk);
        $finish;
    end

endmodule
