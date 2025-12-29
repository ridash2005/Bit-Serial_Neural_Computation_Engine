`timescale 1ns/1ps

module bitserial_nn_tb;

   
  // Parameters (MATCH DUT)
   
  localparam int DATA_W    = 16;
  localparam int N_IN      = 256;
  localparam int N_HIDDEN  = 128;
  localparam int P         = 4;
  localparam int PRECISION = DATA_W;

  localparam int ACC_W = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);
  localparam int WMEM_SIZE = N_HIDDEN * N_IN;

   
  // Clock / Reset
   
  logic clk = 0;
  logic rst_n = 0;

  always #5 clk = ~clk;  // 100 MHz

   
  // AXI-Stream INPUT
   
  logic signed [DATA_W-1:0] s_axis_tdata;
  logic                    s_axis_tvalid;
  logic                    s_axis_tready;
  logic                    s_axis_tlast;

   
  // AXI-Stream OUTPUT
   
  logic signed [ACC_W-1:0]  m_axis_tdata;
  logic                    m_axis_tvalid;
  logic                    m_axis_tready;
  logic                    m_axis_tlast;

   
  // Weight write interface
   
  logic w_wr_en;
  logic [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h;
  logic [$clog2((N_IN>1)?N_IN:2)-1:0]         w_addr_i;
  logic signed [DATA_W-1:0]                  w_data;

   
  // DUT status
   
  logic busy;

   
  // DUT instantiation (EXACT MATCH)
   
  bitserial_nn #(
    .DATA_W(DATA_W),
    .PRECISION(PRECISION),
    .N_IN(N_IN),
    .N_HIDDEN(N_HIDDEN),
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
    .w_data  (w_data),

    .m_axis_tdata (m_axis_tdata),
    .m_axis_tvalid(m_axis_tvalid),
    .m_axis_tready(m_axis_tready),
    .m_axis_tlast (m_axis_tlast),

    .busy(busy)
  );

   
  // Golden reference storage
   
  logic signed [DATA_W-1:0] golden_mem [0:WMEM_SIZE-1];
  logic signed [ACC_W-1:0]  golden_out [0:N_HIDDEN-1];

  function int flat_addr(input int h, input int i);
    flat_addr = h * N_IN + i;
  endfunction

   
  // Weight loading task
   
  task load_weights;
    int h, i;
    begin
      $display("[TB] Loading weights...");
      for (h = 0; h < N_HIDDEN; h++) begin
        for (i = 0; i < N_IN; i++) begin
          @(posedge clk);
          w_wr_en  <= 1;
          w_addr_h <= h;
          w_addr_i <= i;
          w_data   <= $signed(h * 100 + i);
          golden_mem[flat_addr(h,i)] = $signed(h * 100 + i);
        end
      end
      @(posedge clk);
      w_wr_en <= 0;
      $display("[TB] Weight load complete");
    end
  endtask

   
  // Compute golden outputs
   
  task compute_golden(input int base);
    int h, i;
    logic signed [ACC_W+16-1:0] acc;
    begin
      for (h = 0; h < N_HIDDEN; h++) begin
        acc = 0;
        for (i = 0; i < N_IN; i++) begin
          acc += $signed(base + i) * golden_mem[flat_addr(h,i)];
        end
        golden_out[h] = (acc < 0) ? '0 : acc[ACC_W-1:0];
      end
    end
  endtask

   
  // AXI input stream task
   
    task stream_input_vector(input int base);
  int i;
  begin
    $display("[TB] Streaming input vector...");
    for (i = 0; i < N_IN; i++) begin

      s_axis_tdata  <= $signed(base + i);
      s_axis_tlast  <= (i == N_IN-1);
      s_axis_tvalid <= 1;

      // WAIT FOR REAL HANDSHAKE
      do @(posedge clk);
      while (!(s_axis_tvalid && s_axis_tready));

      // Deassert after handshake
      s_axis_tvalid <= 0;
      s_axis_tlast  <= 0;
    end
    $display("[TB] Input streaming done");
  end
endtask

   
  // Main stimulus
   
  int recv_count;
  int timeout;

  initial begin
    $dumpfile("bitserial_nn_tb.vcd");
    $dumpvars(0, bitserial_nn_tb);
    $dumpvars(0, bitserial_nn_tb.dut);

    // defaults
    s_axis_tvalid = 0;
    s_axis_tdata  = 0;
    s_axis_tlast  = 0;
    m_axis_tready = 1; // ALWAYS READY
    w_wr_en = 0;

    // reset
    repeat (5) @(posedge clk);
    rst_n = 1;
    $display("[TB] Reset released");

    // load weights
    load_weights();

    // prepare golden
    compute_golden(0);

    // stream input
    stream_input_vector(0);

    // collect outputs
    recv_count = 0;
    timeout = 0;

    while (recv_count < N_HIDDEN && timeout < 500000) begin
      @(posedge clk);
      timeout++;

      if (m_axis_tvalid) begin
        $display("[OUT] H=%0d DUT=%0d GOLD=%0d LAST=%0b",
                 recv_count,
                 m_axis_tdata,
                 golden_out[recv_count],
                 m_axis_tlast);

        if (m_axis_tdata !== golden_out[recv_count]) begin
          $error(1, "[FAIL] Mismatch at H=%0d", recv_count);
        end

        recv_count++;
      end
    end

    if (recv_count == N_HIDDEN)
      $display("[TB] ✅ SUCCESS: All outputs matched");
    else
      $error(1, "[TB] ❌ TIMEOUT");

    repeat (10) @(posedge clk);
    $finish;
  end

endmodule
