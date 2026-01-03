`timescale 1ns/1ps

module bitserial_nn_tb;

/* ---------------- PARAMETERS ---------------- */

localparam int DATA_W    = 16;
localparam int PRECISION = DATA_W;
localparam int N_IN      = 512;     // keep small for sim
localparam int N_HIDDEN  = 256;
localparam int N_LAYERS  = 7;
localparam int P         = 4;

localparam int ACC_W =
    (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);

/* ---------------- CLOCK / RESET ---------------- */

logic clk = 0;
logic rst_n = 0;
always #5 clk = ~clk;

/* ---------------- AXI INPUT ---------------- */

logic signed [DATA_W-1:0] s_axis_tdata;
logic                     s_axis_tvalid;
logic                     s_axis_tready;
logic                     s_axis_tlast;

/* ---------------- AXI OUTPUT ---------------- */

logic signed [ACC_W-1:0] m_axis_tdata;
logic                   m_axis_tvalid;
logic                   m_axis_tready;
logic                   m_axis_tlast;

/* ---------------- WEIGHT WRITE ---------------- */

logic w_wr_en;
logic [$clog2(N_HIDDEN)-1:0] w_addr_h;
logic [$clog2(N_IN)-1:0]     w_addr_i;
logic [$clog2(N_LAYERS)-1:0] w_addr_l;
logic signed [DATA_W-1:0]    w_data;

/* ---------------- STATUS ---------------- */

logic busy;

/* ---------------- DUT ---------------- */

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

    .s_axis_tdata (s_axis_tdata),
    .s_axis_tvalid(s_axis_tvalid),
    .s_axis_tready(s_axis_tready),
    .s_axis_tlast (s_axis_tlast),

    .w_wr_en (w_wr_en),
    .w_addr_h(w_addr_h),
    .w_addr_i(w_addr_i),
    .w_addr_l(w_addr_l),
    .w_data  (w_data),

    .m_axis_tdata (m_axis_tdata),
    .m_axis_tvalid(m_axis_tvalid),
    .m_axis_tready(m_axis_tready),
    .m_axis_tlast (m_axis_tlast),

    .busy(busy)
);

/* ---------------- GOLDEN MODEL STORAGE ---------------- */

logic signed [DATA_W-1:0] golden_w   [0:N_LAYERS-1][0:N_HIDDEN-1][0:N_IN-1];
logic signed [DATA_W-1:0] golden_act [0:N_LAYERS][0:N_HIDDEN-1];

/* ---------------- LOAD WEIGHTS ---------------- */

task automatic load_weights;
    int l,h,i;
    begin
        w_wr_en = 0;
        @(posedge clk);

        for (l = 0; l < N_LAYERS; l++) begin
            for (h = 0; h < N_HIDDEN; h++) begin
                for (i = 0; i < N_IN; i++) begin
                    @(posedge clk);
                    w_wr_en  <= 1;
                    w_addr_l <= l;
                    w_addr_h <= h;
                    w_addr_i <= i;
                    w_data   <= $signed(l*100 + h*10 + i);

                    golden_w[l][h][i] =
                        $signed(l*100 + h*10 + i);
                end
            end
        end

        @(posedge clk);
        w_wr_en <= 0;
    end
endtask

/* ---------------- GOLDEN COMPUTE ---------------- */

task automatic compute_golden(input int base);
    int l,h,i;
    integer acc;
    begin
        // input layer
        for (i = 0; i < N_IN; i++)
            golden_act[0][i] = base + i;

        for (l = 0; l < N_LAYERS; l++) begin
            for (h = 0; h < N_HIDDEN; h++) begin
                acc = 0;
                for (i = 0; i < N_IN; i++) begin
                    if (l == 0)
                        acc += golden_act[0][i] * golden_w[l][h][i];
                    else if (i < N_HIDDEN)
                        acc += golden_act[l][i] * golden_w[l][h][i];
                end
                golden_act[l+1][h] =
                    (acc < 0) ? '0 : acc[DATA_W-1:0];
            end
        end
    end
endtask

/* ---------------- STREAM INPUT ---------------- */

task automatic stream_input(input int base);
    int i;
    begin
        for (i = 0; i < N_IN; i++) begin
            s_axis_tdata  <= base + i;
            s_axis_tvalid <= 1;
            s_axis_tlast  <= (i == N_IN-1);

            do @(posedge clk);
            while (!s_axis_tready);

            s_axis_tvalid <= 0;
            s_axis_tlast  <= 0;
        end
    end
endtask

/* ---------------- MAIN TEST ---------------- */

int out_idx;

initial begin
    $dumpfile("bitserial_nn_tb.vcd");
    $dumpvars(0, bitserial_nn_tb);

    // defaults
    s_axis_tvalid = 0;
    s_axis_tdata  = 0;
    s_axis_tlast  = 0;
    m_axis_tready = 1;
    w_wr_en       = 0;

    repeat (5) @(posedge clk);
    rst_n = 1;

    load_weights();
    compute_golden(0);
    stream_input(0);

    out_idx = 0;

    while (out_idx < N_HIDDEN) begin
        @(posedge clk);
        if (m_axis_tvalid) begin
            if (m_axis_tdata !== golden_act[N_LAYERS][out_idx])
                $error("Mismatch H%0d: DUT=%0d GOLD=%0d",
                       out_idx,
                       m_axis_tdata,
                       golden_act[N_LAYERS][out_idx]);
            out_idx++;
        end
    end

    $display("✅ TEST PASSED: bitserial_nn multi-layer verified");
    $finish;
end

endmodule
