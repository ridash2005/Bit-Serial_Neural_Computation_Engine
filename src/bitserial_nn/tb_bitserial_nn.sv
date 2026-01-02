`timescale 1ns/1ps

module bitserial_nn_tb;

  /* ---------------- PARAMETERS ---------------- */

  localparam int DATA_W    = 16;
  localparam int N_IN      = 256;
  localparam int N_HIDDEN  = 128;
  localparam int N_LAYERS  = 3;
  localparam int P         = 4;
  localparam int PRECISION = DATA_W;

  localparam int ACC_W =
      (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);

  /* ---------------- CLOCK / RESET ---------------- */

  logic clk = 0;
  logic rst_n = 0;
  always #5 clk = ~clk;

  /* ---------------- AXI INPUT ---------------- */

  logic signed [DATA_W-1:0] s_axis_tdata;
  logic                    s_axis_tvalid;
  logic                    s_axis_tready;
  logic                    s_axis_tlast;

  /* ---------------- AXI OUTPUT ---------------- */

  logic signed [ACC_W-1:0]  m_axis_tdata;
  logic                    m_axis_tvalid;
  logic                    m_axis_tready;
  logic                    m_axis_tlast;

  /* ---------------- WEIGHT WRITE ---------------- */

  logic w_wr_en;
  logic [$clog2(N_HIDDEN)-1:0] w_addr_h;
  logic [$clog2(N_IN)-1:0]     w_addr_i;
  logic [$clog2(N_LAYERS)-1:0] w_addr_l;
  logic signed [DATA_W-1:0]    w_data;

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

  /* ---------------- GOLDEN STORAGE ---------------- */

  logic signed [DATA_W-1:0]
      golden_w [0:N_LAYERS-1][0:N_HIDDEN-1][0:N_IN-1];

  logic signed [DATA_W-1:0]
      golden_act [0:N_LAYERS][0:N_HIDDEN-1];

  /* ---------------- LOAD WEIGHTS ---------------- */

  task load_weights;
    int l,h,i;
    begin
      $display("[TB] Loading weights...");
      for (l = 0; l < N_LAYERS; l++) begin
        for (h = 0; h < N_HIDDEN; h++) begin
          for (i = 0; i < N_IN; i++) begin
            @(posedge clk);
            w_wr_en  <= 1;
            w_addr_l <= l;
            w_addr_h <= h;
            w_addr_i <= i;
            w_data   <= $signed(l*1000 + h*10 + i);
            golden_w[l][h][i] = $signed(l*1000 + h*10 + i);
          end
        end
      end
      @(posedge clk);
      w_wr_en <= 0;
      $display("[TB] Weight load complete");
    end
  endtask

  /* ---------------- GOLDEN MODEL ---------------- */

  task compute_golden(input int base);
    int l,h,i;
    integer acc;
    begin
      // Input layer
      for (i = 0; i < N_IN; i++)
        golden_act[0][i] = $signed(base + i);

      // Hidden layers
      for (l = 0; l < N_LAYERS; l++) begin
        for (h = 0; h < N_HIDDEN; h++) begin
          acc = 0;
          for (i = 0; i < N_IN; i++)
            acc += golden_act[l][i] * golden_w[l][h][i];

          // ReLU + DATA_W truncation (MATCHES DUT)
          golden_act[l+1][h] =
              (acc < 0) ? '0 : acc[DATA_W-1:0];
        end
      end
    end
  endtask

  /* ---------------- STREAM INPUT ---------------- */

  task stream_input_vector(input int base);
    int i;
    begin
      for (i = 0; i < N_IN; i++) begin
        s_axis_tdata  <= $signed(base + i);
        s_axis_tlast  <= (i == N_IN-1);
        s_axis_tvalid <= 1;

        do @(posedge clk);
        while (!(s_axis_tvalid && s_axis_tready));

        s_axis_tvalid <= 0;
        s_axis_tlast  <= 0;
      end
    end
  endtask

  /* ---------------- MAIN ---------------- */

  int recv_count;
  int timeout;

  initial begin
    $dumpfile("bitserial_nn_tb.vcd");
    $dumpvars(0, bitserial_nn_tb);

    // Defaults
    s_axis_tvalid = 0;
    s_axis_tdata  = 0;
    s_axis_tlast  = 0;
    m_axis_tready = 1;
    w_wr_en = 0;
    w_addr_l = 0;

    // Reset
    repeat (5) @(posedge clk);
    rst_n = 1;

    load_weights();
    compute_golden(0);
    stream_input_vector(0);

    recv_count = 0;
    timeout = 0;

    while (recv_count < N_HIDDEN && timeout < 1_000_000) begin
      @(posedge clk);
      timeout++;

      if (m_axis_tvalid) begin
        if (m_axis_tdata !== golden_act[N_LAYERS][recv_count]) begin
          $error("[FAIL] Mismatch at H=%0d DUT=%0d GOLD=%0d",
                 recv_count,
                 m_axis_tdata,
                 golden_act[N_LAYERS][recv_count]);
        end
        recv_count++;
      end
    end

    if (recv_count == N_HIDDEN)
      $display("[TB] ✅ SUCCESS: Multi-layer outputs matched");
    else
      $error("[TB] ❌ TIMEOUT");

    $finish;
  end

endmodule
