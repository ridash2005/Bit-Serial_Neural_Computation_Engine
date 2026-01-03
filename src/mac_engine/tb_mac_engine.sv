`timescale 1ns/1ps

module tb_mac_engine;

    /* ---------------- PARAMETERS ---------------- */

    parameter int DATA_W     = 16;
    parameter int PRECISION  = DATA_W;
    parameter int N_IN       = 10;
    parameter int N_HIDDEN   = 8;
    parameter int N_LAYERS   = 3;
    parameter int P          = 3;

    localparam int ACC_W =
        (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);

    /* ---------------- CLOCK / RESET ---------------- */

    logic clk = 0;
    logic rst_n;

    always #5 clk = ~clk;

    /* ---------------- DUT INTERFACE ---------------- */

    logic [$clog2(N_LAYERS)-1:0] layer_idx;
    logic start_compute;

    logic signed [N_IN*DATA_W-1:0] invec_bus;

    logic [$clog2(N_LAYERS*N_HIDDEN*N_IN)-1:0] wmem_raddr;
    logic signed [DATA_W-1:0] wmem_rdata;

    logic signed [ACC_W-1:0] out_data;
    logic out_valid;
    logic out_ready;

    logic busy;
    logic layer_done;

    /* ---------------- DUT ---------------- */

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

    /* ---------------- TEST STORAGE ---------------- */

    logic signed [DATA_W-1:0] input_vec [N_IN];
    logic signed [DATA_W-1:0] weights   [N_LAYERS][N_HIDDEN][N_IN];

    logic signed [ACC_W-1:0] expected   [N_LAYERS][N_HIDDEN];
    logic signed [ACC_W-1:0] captured   [N_LAYERS][N_HIDDEN];

    int result_idx;

    /* ---------------- WEIGHT MEMORY MODEL ---------------- */

    always_comb begin
        int flat, l, r, h, i;
        flat = wmem_raddr;

        l = flat / (N_HIDDEN*N_IN);
        r = flat % (N_HIDDEN*N_IN);
        h = r / N_IN;
        i = r % N_IN;

        if (l < N_LAYERS && h < N_HIDDEN && i < N_IN)
            wmem_rdata = weights[l][h][i];
        else
            wmem_rdata = '0;
    end

    /* ---------------- OUTPUT CAPTURE ---------------- */

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            result_idx <= 0;
        end
        else if (out_valid && out_ready) begin
            captured[layer_idx][result_idx] <= out_data;
            $display("[%0t] L%0d H%0d = %0d",
                     $time, layer_idx, result_idx, out_data);
            result_idx <= result_idx + 1;
        end
    end

    /* ---------------- GOLDEN MODEL ---------------- */

    task compute_expected;
        int l, h, i;
        longint acc;
        begin
            for (l = 0; l < N_LAYERS; l++) begin
                for (h = 0; h < N_HIDDEN; h++) begin
                    acc = 0;
                    for (i = 0; i < N_IN; i++)
                        acc += longint'(input_vec[i]) *
                               longint'(weights[l][h][i]);
                    expected[l][h] = acc[ACC_W-1:0];
                end
            end
        end
    endtask

    /* ---------------- RANDOM DATA ---------------- */

    task randomize_data;
        int l, h, i;
        begin
            for (i = 0; i < N_IN; i++) begin
                input_vec[i] = $random % 20 - 10;
                invec_bus[i*DATA_W +: DATA_W] = input_vec[i];
            end

            for (l = 0; l < N_LAYERS; l++)
                for (h = 0; h < N_HIDDEN; h++)
                    for (i = 0; i < N_IN; i++)
                        weights[l][h][i] = $random % 10 - 5;

            compute_expected();
        end
    endtask

    /* ---------------- RUN ONE LAYER ---------------- */

    task run_layer(input int l);
        begin
            $display("\n[TB] ===== RUN LAYER %0d =====", l);

            layer_idx   = l;
            result_idx  = 0;
            out_ready   = 1;

            @(posedge clk);
            start_compute = 1;
            @(posedge clk);
            start_compute = 0;

            wait(layer_done);
            $display("[TB] Layer %0d DONE at %0t", l, $time);

            repeat(5) @(posedge clk);
        end
    endtask

    /* ---------------- VERIFY ONE LAYER ---------------- */

    task verify_layer(input int l);
        int errors;
        begin
          errors=0;
            for (int h = 0; h < N_HIDDEN; h++) begin
                if (captured[l][h] !== expected[l][h]) begin
                    $error("L%0d H%0d MISMATCH: got %0d exp %0d",
                           l, h, captured[l][h], expected[l][h]);
                    errors++;
                end
                else begin
                     $display("L%0d H%0d MATCHED: got %0d exp %0d",
                           l, h, captured[l][h], expected[l][h]);
                end
            end

            if (errors == 0)
                $display("[TB] ✓ LAYER %0d PASSED", l);
        end
    endtask

    /* ---------------- MAIN TEST ---------------- */

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_mac_engine);

        rst_n = 0;
        start_compute = 0;
        out_ready = 1;
        invec_bus = '0;
        layer_idx = '0;

        repeat(3) @(posedge clk);
        rst_n = 1;

        randomize_data();

        for (int l = 0; l < N_LAYERS; l++) begin
            run_layer(l);
            verify_layer(l);
        end

        $display("\n[TB] ALL LAYERS COMPLETE");
        $finish;
    end

    /* ---------------- PROTOCOL ASSERTIONS ---------------- */

    // start_compute must not assert while busy
    property p_no_start_when_busy;
        @(posedge clk) disable iff (!rst_n)
        busy |-> !start_compute;
    endproperty
    assert property (p_no_start_when_busy);

    // out_data must remain stable when stalled
    property p_stable_when_stalled;
        @(posedge clk) disable iff (!rst_n)
        (out_valid && !out_ready) |=> $stable(out_data);
    endproperty
    assert property (p_stable_when_stalled);

endmodule
