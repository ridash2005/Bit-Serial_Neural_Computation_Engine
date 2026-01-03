`timescale 1ns/1ps

module mac_engine #(
    parameter int unsigned DATA_W    = 16,
    parameter int unsigned PRECISION = DATA_W,
    parameter int unsigned N_IN      = 128,
    parameter int unsigned N_HIDDEN  = 64,
    parameter int unsigned N_LAYERS  = 3,
    parameter int unsigned P         = 4
)(
    input  logic clk,
    input  logic rst_n,

    // Layer index
    input  logic [$clog2(N_LAYERS)-1:0] layer_idx,

    // control
    input  logic start_compute,

    // input vector
    input  logic signed [N_IN*DATA_W-1:0] invec_bus,

    // weight memory read
    output logic [$clog2(N_LAYERS*N_HIDDEN*N_IN)-1:0] wmem_raddr,
    input  logic signed [DATA_W-1:0] wmem_rdata,

    // output stream (to AXI adapter / ReLU)
    output logic signed [(2*DATA_W)+$clog2((N_IN>1)?N_IN:2)-1:0] out_data,
    output logic out_valid,
    input  logic out_ready,

    // status
    output logic busy,
    output logic layer_done
);


    // Local parameters

    localparam int IN_CNT_W = $clog2((N_IN>1)?N_IN:2);
    localparam int ACC_W    = (2*DATA_W) + IN_CNT_W;
    localparam int BIT_W    = $clog2((PRECISION>1)?PRECISION:2);
    localparam int HID_W    = $clog2((N_HIDDEN>1)?N_HIDDEN:2);
    localparam int P_W      = $clog2((P>1)?P:2);
    localparam int LSTRIDE = N_HIDDEN * N_IN;

    typedef enum logic [1:0] { IDLE, PROC, STREAM } state_t;
    state_t state, state_n;

  
    // State / counters

    logic [HID_W-1:0]    cur_hidden;
    logic [IN_CNT_W-1:0] cur_input;
    logic [BIT_W-1:0]    bit_idx;

    logic                bit_active;
    logic                mem_read_pending;
    logic                mem_wait;
    logic [P_W-1:0]      mem_lane;

    logic signed [DATA_W-1:0] a_val;
    logic signed [DATA_W-1:0] abs_b [P];
    logic                     sign_prod [P];
    logic signed [ACC_W-1:0]  partial [P];
    logic signed [ACC_W-1:0]  hidden_accum [N_HIDDEN];

    // completion counter and memory index
    logic [HID_W:0]   out_index;      // completion detect (extra bit)
    logic [HID_W-1:0] out_mem_index;  // exact-width memory index

   
    // Bit-serial helpers

    wire signed [DATA_W-1:0] abs_a =
        a_val[DATA_W-1] ? -a_val : a_val;

    wire signed [ACC_W-1:0] shifted_abs_a =
        $signed({{(ACC_W-DATA_W){1'b0}}, abs_a}) << bit_idx;


    // Next-state logic

    always_comb begin
        state_n = state;
        case (state)
            IDLE:   if (start_compute) state_n = PROC;

            PROC: begin
                if (bit_active &&
                    (bit_idx == PRECISION-1) &&
                    (cur_input + 1 >= N_IN) &&
                    (cur_hidden + P >= N_HIDDEN))
                    state_n = STREAM;
            end

            STREAM: begin
                if (out_index >= N_HIDDEN)
                    state_n = IDLE;
            end

            default: state_n = IDLE;
        endcase
    end

    
    // Sequential logic
    
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            state <= IDLE;
            busy  <= 1'b0;
            layer_done <= 1'b0;

            cur_hidden <= '0;
            cur_input  <= '0;
            bit_idx    <= '0;
            bit_active <= 1'b0;

            mem_read_pending <= 1'b0;
            mem_wait         <= 1'b0;
            mem_lane         <= '0;

            out_valid     <= 1'b0;
            out_index     <= '0;
            out_mem_index <= '0;   // FIX
            out_data      <= '0;

            a_val      <= '0;
            wmem_raddr <= '0;

            for (int i=0; i<N_HIDDEN; i++)
                hidden_accum[i] <= '0;

            for (int i=0; i<P; i++) begin
                abs_b[i]     <= '0;
                sign_prod[i] <= '0;
                partial[i]   <= '0;
            end

        end else begin
            state <= state_n;
            busy  <= (state_n != IDLE);

            case (state)

                // ---------------- IDLE ----------------
                IDLE: begin
                    cur_hidden   <= '0;
                    cur_input    <= '0;
                    out_index    <= '0;
                    out_mem_index<= '0;   // FIX
                    out_valid    <= 1'b0;
                    bit_active   <= 1'b0;
                    mem_read_pending <= 1'b0;
                    layer_done <= 1'b0;

                    if (start_compute) begin
                        for (int i=0; i<N_HIDDEN; i++)
                            hidden_accum[i] <= '0;
                    end
                end

                // ---------------- PROC ----------------
                PROC: begin
                    // start memory read
                    if (!bit_active && !mem_read_pending &&
                        cur_hidden < N_HIDDEN) begin

                        mem_read_pending <= 1'b1;
                        mem_lane <= '0;
                        mem_wait <= 1'b1;

                        a_val <= invec_bus[cur_input*DATA_W +: DATA_W];
                        wmem_raddr <= (layer_idx * LSTRIDE)+(cur_hidden * N_IN) + cur_input;
                    end

                    // memory pipeline
                    if (mem_read_pending) begin
                        if (mem_wait) begin
                            mem_wait <= 1'b0;
                        end else begin
                            abs_b[mem_lane] <=
                                wmem_rdata[DATA_W-1] ? -wmem_rdata : wmem_rdata;

                            sign_prod[mem_lane] <=
                                a_val[DATA_W-1] ^ wmem_rdata[DATA_W-1];

                            if ((mem_lane + 1 < P) &&
                                (cur_hidden + mem_lane + 1 < N_HIDDEN)) begin
                                mem_lane <= mem_lane + 1'b1;
                                mem_wait <= 1'b1;
                                wmem_raddr <=
                                    (layer_idx * LSTRIDE)+(cur_hidden + mem_lane + 1) * N_IN + cur_input;
                            end else begin
                                mem_read_pending <= 1'b0;
                                bit_active <= 1'b1;
                                bit_idx <= '0;
                                for (int i=0; i<P; i++)
                                    partial[i] <= '0;
                            end
                        end
                    end

                    // bit-serial accumulation
                    if (bit_active) begin
                        for (int unsigned i=0; i<P; i++) begin
                            if (cur_hidden + i < N_HIDDEN) begin
                                if (abs_b[i][bit_idx])
                                    partial[i] <= partial[i] + shifted_abs_a;
                            end
                        end

                        if (bit_idx == PRECISION-1) begin
                            bit_active <= 1'b0;

                            for (int unsigned i=0; i<P; i++) begin
                                if (cur_hidden + i < N_HIDDEN) begin
                                    automatic logic [ACC_W-1:0] final_p;
                                    final_p =
                                        abs_b[i][bit_idx] ?
                                        (partial[i] + shifted_abs_a) :
                                        partial[i];

                                    hidden_accum[cur_hidden+i] <=
                                        sign_prod[i] ?
                                        (hidden_accum[cur_hidden+i] - final_p) :
                                        (hidden_accum[cur_hidden+i] + final_p);
                                end
                            end

                            if (cur_input + 1 >= N_IN) begin
                                cur_input  <= '0;
                                cur_hidden <= cur_hidden + P;
                            end else begin
                                cur_input <= cur_input + 1'b1;
                            end
                        end else begin
                            bit_idx <= bit_idx + 1'b1;
                        end
                    end
                end

                // ---------------- STREAM ----------------
                STREAM: begin
                    if (out_index < N_HIDDEN) begin
                        if (!out_valid) begin
                            // FIX: use memory index
                            out_data  <= hidden_accum[out_mem_index];
                            out_valid <= 1'b1;
                        end
                        else if (out_ready) begin
                            out_index <= out_index + 1'b1;

                            if (out_index + 1 < N_HIDDEN) begin
                                // FIX: advance memory index safely
                                out_mem_index <= out_mem_index + 1'b1;
                                out_data      <= hidden_accum[out_mem_index + 1'b1];
                                out_valid     <= 1'b1;
                            end else begin
                                out_valid <= 1'b0;
                                layer_done <= 1'b1;
                            end
                        end
                    end else begin
                        out_valid <= 1'b0;
                    end
                end
            endcase
        end
    end

endmodule