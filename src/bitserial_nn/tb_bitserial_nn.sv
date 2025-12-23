//--------------------------------
// To be updated fully 
//----------------------------------

`timescale 1ns/1ps

module bitserial_nn_tb;

  
  // Parameters
  localparam integer DATA_W    = 16;
  localparam integer N_IN      = 128;
  localparam integer N_HIDDEN  = 64;
  localparam integer N_OUT     = 10;
  localparam integer P         = 4;
  localparam integer PRECISION = DATA_W;

  localparam integer ACC_W       = (2*DATA_W) + $clog2((N_IN>1)?N_IN:2);
  localparam integer WMEM_SIZE   = N_HIDDEN * N_IN;

  
  // DUT I/O
  reg clk = 0;
  reg rst_n = 0;

  reg signed [DATA_W-1:0] data_in = 0;
  reg data_in_valid = 0;
  reg start = 0;

  reg w_wr_en = 0;
  reg [$clog2((N_HIDDEN>1)?N_HIDDEN:2)-1:0] w_addr_h = 0;
  reg [$clog2((N_IN>1)?N_IN:2)-1:0] w_addr_i = 0;
  reg signed [DATA_W-1:0] w_data = 0;

  reg signed [ACC_W-1:0] golden_out_ref [0:N_HIDDEN-1];

  wire signed [ACC_W-1:0] out_data;
  wire out_valid;
  wire busy;

  integer vec_base, recv_count, timeout_counter;

  
  // Instantiate DUT
  bitserial_nn #(
      .DATA_W(DATA_W),
      .N_IN(N_IN),
      .N_HIDDEN(N_HIDDEN),
      .N_OUT(N_OUT),
      .P(P),
      .PRECISION(PRECISION)
  ) dut (
      .clk(clk), .rst_n(rst_n),
      .data_in(data_in),
      .data_in_valid(data_in_valid),
      .start(start),
      .w_wr_en(w_wr_en),
      .w_addr_h(w_addr_h),
      .w_addr_i(w_addr_i),
      .w_data(w_data),
      .out_data(out_data),
      .out_valid(out_valid),
      .busy(busy)
  );

 
  // Clock
  always #5 clk = ~clk; // 100 MHz

 
  // Golden memory for weights
  reg signed [DATA_W-1:0] golden_mem [0:WMEM_SIZE-1];
  integer i, h, k;

  function integer flat_addr;
    input integer hh;
    input integer ii;
    begin
      flat_addr = hh * N_IN + ii;
    end
  endfunction

  
  // Weight write + logging
  task load_weights;
    integer val;
    begin
      $display("[TB] Starting weight load...");
      for (h = 0; h < N_HIDDEN; h = h + 1) begin
        for (k = 0; k < N_IN; k = k + 1) begin
          // prepare write (blocking assignments so values are immediate)
          val = (h * 100) + k;
          w_addr_h = h;
          w_addr_i = k;
          w_data   = $signed(val);
          w_wr_en  = 1;

          // update golden memory immediately 
          golden_mem[flat_addr(h,k)] = w_data;

          $display("[WRITE-W] t=%0t H=%0d I=%0d DATA=%0d", $time, h, k, w_data);

          // perform the write on rising edge
          @(posedge clk);

          // deassert write
          w_wr_en = 0;
        end
      end
      $display("[TB] Completed writing all %0d weights", WMEM_SIZE);
    end
  endtask

  
  // Input feeding + logging
  // Each sample is valid for one cycle (asserted for that cycle).
  task feed_input_vector;
    input integer base;
    integer idx;
    begin
      $display("[TB] Streaming input vector base=%0d", base);
      for (idx = 0; idx < N_IN; idx = idx + 1) begin
        // prepare value (blocking)
        data_in = $signed(idx + base);
        data_in_valid = 1;
        $display("[WRITE-IN] t=%0t IDX=%0d DATA=%0d", $time, idx, data_in);

        // sample captured by input_buffer on posedge
        @(posedge clk);

        // deassert valid immediately after the cycle so each sample is precisely one cycle long
        data_in_valid = 0;
        data_in = 0;
      end

      // small margin to allow input_buffer to finish
      repeat (4) @(posedge clk);
      $display("[TB] Finished streaming input vector");
    end
  endtask

  
  // Golden output computation
  task compute_golden_outputs;
    input integer base;
    output reg signed [ACC_W-1:0] arr [0:N_HIDDEN-1];
    integer hh, ii;
    // make accumulator wide enough: ACC_W + 16 bits headroom
    reg signed [ACC_W+16-1:0] sum_local;
    reg signed [DATA_W-1:0] wt;
    reg signed [31:0] inp;
    begin
      $display("[TB] Computing golden outputs (base=%0d)...", base);
      for (hh = 0; hh < N_HIDDEN; hh = hh + 1) begin
        sum_local = 0;
        for (ii = 0; ii < N_IN; ii = ii + 1) begin
          wt  = golden_mem[flat_addr(hh, ii)];
          inp = $signed(ii + base);
          sum_local = sum_local + (inp * wt);
        end
        // Apply ReLU: clamp negatives to 0
        if (sum_local < 0)
          arr[hh] = $signed({{(ACC_W){1'b0}}});
        else
          // truncate/assign into ACC_W width
          arr[hh] = $signed(sum_local[ACC_W-1:0]);

        $display("[GOLD] H=%0d VAL=%0d", hh, arr[hh]);
      end
    end
  endtask

 
  // Main stimulus
  initial begin
    $dumpfile("bitserial_nn_tb.vcd");
    $dumpvars(0, bitserial_nn_tb);

    // Reset pulse
    rst_n = 0;
    repeat (5) @(posedge clk);
    @(posedge clk);
    rst_n = 1;
    $display("[TB] Reset released at time %0t", $time);

    // 1) load deterministic weights
    load_weights();

    // 2) compute golden outputs for the input vector we'll feed
    vec_base = 0;
    compute_golden_outputs(vec_base, golden_out_ref);

    // 3) feed input vector (streaming)
    feed_input_vector(vec_base);

    // 4) start MAC computation (after streaming)
    @(posedge clk);
    start = 1;
    $display("[TB] Asserted start at %0t", $time);
    @(posedge clk);
    start = 0;

    // 5) collect outputs and compare
    recv_count = 0;
    timeout_counter = 0;
    while (recv_count < N_HIDDEN && timeout_counter < 200000) begin
      @(posedge clk);
      timeout_counter = timeout_counter + 1;
      if (out_valid) begin
        $display("[READ] t=%0t OUT_IDX=%0d DUT=%0d GOLD=%0d", $time, recv_count, $signed(out_data), $signed(golden_out_ref[recv_count]));
        if ($signed(out_data) !== $signed(golden_out_ref[recv_count])) begin
          $display("[FAIL] H=%0d EXP=%0d GOT=%0d", recv_count, golden_out_ref[recv_count], out_data);
        end else begin
          $display("[PASS] H=%0d VAL=%0d", recv_count, out_data);
        end
        recv_count = recv_count + 1;
      end
    end

    if (recv_count == N_HIDDEN) begin
      $display("[TB] SUCCESS: Received all %0d outputs", N_HIDDEN);
    end else begin
      $display("[TB] ERROR: Timeout, received %0d / %0d", recv_count, N_HIDDEN);
    end

    repeat (10) @(posedge clk);
    $finish;
  end

endmodule
