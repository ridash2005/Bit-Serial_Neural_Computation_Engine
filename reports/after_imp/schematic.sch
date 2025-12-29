# File saved with Nlview 7.8.0 2024-04-26 e1825d835c VDI=44 GEI=38 GUI=JA:21.0 threadsafe
# 
# non-default properties - (restore without -noprops)
property -colorscheme classic
property attrcolor #000000
property attrfontsize 8
property autobundle 1
property backgroundcolor #ffffff
property boxcolor0 #000000
property boxcolor1 #000000
property boxcolor2 #000000
property boxinstcolor #000000
property boxpincolor #000000
property buscolor #008000
property closeenough 5
property createnetattrdsp 2048
property decorate 1
property elidetext 40
property fillcolor1 #ffffcc
property fillcolor2 #dfebf8
property fillcolor3 #f0f0f0
property gatecellname 2
property instattrmax 30
property instdrag 15
property instorder 1
property marksize 12
property maxfontsize 12
property maxzoom 5
property netcolor #19b400
property objecthighlight0 #ff00ff
property objecthighlight1 #ffff00
property objecthighlight2 #00ff00
property objecthighlight3 #0095ff
property objecthighlight4 #8000ff
property objecthighlight5 #ffc800
property objecthighlight7 #00ffff
property objecthighlight8 #ff00ff
property objecthighlight9 #ccccff
property objecthighlight10 #0ead00
property objecthighlight11 #cefc00
property objecthighlight12 #9e2dbe
property objecthighlight13 #ba6a29
property objecthighlight14 #fc0188
property objecthighlight15 #02f990
property objecthighlight16 #f1b0fb
property objecthighlight17 #fec004
property objecthighlight18 #149bff
property objecthighlight19 #eb591b
property overlaycolor #19b400
property pbuscolor #000000
property pbusnamecolor #000000
property pinattrmax 20
property pinorder 2
property pinpermute 0
property portcolor #000000
property portnamecolor #000000
property ripindexfontsize 4
property rippercolor #000000
property rubberbandcolor #000000
property rubberbandfontsize 12
property selectattr 0
property selectionappearance 2
property selectioncolor #0000ff
property sheetheight 44
property sheetwidth 68
property showmarks 1
property shownetname 0
property showpagenumbers 1
property showripindex 1
property timelimit 1
#
module new bitserial_nn work:bitserial_nn:NOFILE -nosplit
load symbol OBUF hdi_primitives BUF pin O output pin I input fillcolor 1
load symbol BUFGCE hdi_primitives BUFIF1 pin O output pin CE input.top pin I input fillcolor 1
load symbol IBUF {hdi_primitives:netlist:no file specified} HIERBOX pin O output.right pin I input.left fillcolor 2
load symbol IBUF {hdi_primitives:abstract:no file specified} HIERBOX pin O output.right pin I input.left fillcolor 2
load symbol LUT1 hdi_primitives BOX pin O output.right pin I0 input.left fillcolor 1
load symbol LUT4 hdi_primitives BOX pin O output.right pin I0 input.left pin I1 input.left pin I2 input.left pin I3 input.left fillcolor 1
load symbol LUT5 hdi_primitives BOX pin O output.right pin I0 input.left pin I1 input.left pin I2 input.left pin I3 input.left pin I4 input.left fillcolor 1
load symbol LUT6 hdi_primitives BOX pin O output.right pin I0 input.left pin I1 input.left pin I2 input.left pin I3 input.left pin I4 input.left pin I5 input.left fillcolor 1
load symbol LUT2 hdi_primitives BOX pin O output.right pin I0 input.left pin I1 input.left fillcolor 1
load symbol FDRE hdi_primitivesR,_INVPIN_ GEN pin Q output.right pin C input.clk.left pin CE input.left pin D input.left pin R input.neg.left fillcolor 1
load symbol input_buffer work:input_buffer:NOFILE HIERBOX pin a_val[0]_i_7_0 input.left pin a_val_reg[0]_i_55_0 input.left pin a_val_reg[10]_i_49_0 input.left pin a_val_reg[10]_i_49_1 input.left pin a_val_reg[11]_i_49_0 input.left pin a_val_reg[11]_i_49_1 input.left pin a_val_reg[12]_i_49_0 input.left pin a_val_reg[12]_i_49_1 input.left pin a_val_reg[13]_i_49_0 input.left pin a_val_reg[13]_i_49_1 input.left pin a_val_reg[14]_i_49_0 input.left pin a_val_reg[14]_i_49_1 input.left pin a_val_reg[1]_i_36_0 input.left pin a_val_reg[1]_i_39_0 input.left pin a_val_reg[2]_i_13_0 input.left pin a_val_reg[3]_i_48_0 input.left pin a_val_reg[3]_i_48_1 input.left pin a_val_reg[4]_i_28_0 input.left pin a_val_reg[4]_i_29_0 input.left pin a_val_reg[5]_i_18_0 input.left pin a_val_reg[6]_i_38_0 input.left pin a_val_reg[6]_i_41_0 input.left pin a_val_reg[7]_i_25_0 input.left pin a_val_reg[7]_i_8_0 input.left pin a_val_reg[8]_i_20_0 input.left pin a_val_reg[8]_i_49_0 input.left pin a_val_reg[8]_i_49_1 input.left pin a_val_reg[9]_i_49_0 input.left pin a_val_reg[9]_i_49_1 input.left pin busy_OBUF input.left pin clk_IBUF_BUFG input.left pin p_0_in input.left pin rst_n_IBUF input.left pin s_axis_tlast_IBUF input.left pin s_axis_tvalid_IBUF input.left pin vector_done output.right pin wr_ptr01_out input.left pinBus D output.right [15:0] pinBus Q input.left [7:0] pinBus inbuf_reg[255][15]_0 input.left [15:0] boxcolor 1 fillcolor 2 minwidth 13%
load symbol mac_engine work:mac_engine:NOFILE HIERBOX pin busy_OBUF output.right pin clk_IBUF_BUFG input.left pin cur_input_reg[0]_rep_0 output.right pin cur_input_reg[0]_rep__0_0 output.right pin cur_input_reg[0]_rep__10_0 output.right pin cur_input_reg[0]_rep__1_0 output.right pin cur_input_reg[0]_rep__2_0 output.right pin cur_input_reg[0]_rep__3_0 output.right pin cur_input_reg[0]_rep__4_0 output.right pin cur_input_reg[0]_rep__5_0 output.right pin cur_input_reg[0]_rep__6_0 output.right pin cur_input_reg[0]_rep__7_0 output.right pin cur_input_reg[0]_rep__8_0 output.right pin cur_input_reg[0]_rep__9_0 output.right pin cur_input_reg[1]_rep_0 output.right pin cur_input_reg[1]_rep__0_0 output.right pin cur_input_reg[1]_rep__10_0 output.right pin cur_input_reg[1]_rep__11_0 output.right pin cur_input_reg[1]_rep__1_0 output.right pin cur_input_reg[1]_rep__2_0 output.right pin cur_input_reg[1]_rep__3_0 output.right pin cur_input_reg[1]_rep__4_0 output.right pin cur_input_reg[1]_rep__5_0 output.right pin cur_input_reg[1]_rep__7_0 output.right pin cur_input_reg[1]_rep__8_0 output.right pin cur_input_reg[1]_rep__9_0 output.right pin cur_input_reg[2]_rep_0 output.right pin cur_input_reg[2]_rep__0_0 output.right pin cur_input_reg[2]_rep__1_0 output.right pin cur_input_reg[2]_rep__2_0 output.right pin cur_input_reg[3]_rep_0 output.right pin lopt output.right pin m_axis_tready_IBUF input.left pin m_axis_tvalid_OBUF input.left pin mac_out_ready input.left pin mac_out_valid output.right pin out_valid_reg_0 output.right pin p_0_in output.right pin rst_n_IBUF input.left pin s_axis_tready_OBUF output.right pin s_axis_tvalid_IBUF input.left pin vector_done input.left pin wmem_raddr_reg[12]_0 output.right pin wmem_raddr_reg[12]_1 output.right pin wmem_raddr_reg[12]_2 output.right pin wmem_raddr_reg[12]_3 output.right pin wmem_raddr_reg[12]_4 output.right pin wmem_raddr_reg[12]_5 output.right pin wmem_raddr_reg[12]_6 output.right pin wmem_raddr_reg[12]_7 output.right pin wmem_raddr_reg[13]_0 output.right pin wmem_raddr_reg[13]_1 output.right pin wmem_raddr_reg[13]_2 output.right pin wmem_raddr_reg[13]_3 output.right pin wmem_raddr_reg[13]_4 output.right pin wmem_raddr_reg[13]_5 output.right pin wmem_raddr_reg[13]_6 output.right pin wmem_raddr_reg[13]_7 output.right pin wmem_raddr_reg[13]_8 output.right pin wmem_raddr_reg[14]_0 output.right pin wmem_raddr_reg[14]_1 output.right pin wmem_raddr_reg[14]_2 output.right pin wmem_raddr_reg[14]_3 output.right pin wmem_raddr_reg[14]_4 output.right pin wmem_raddr_reg[14]_5 output.right pin wmem_raddr_reg[14]_6 output.right pin wmem_raddr_reg[14]_7 output.right pin wr_ptr01_out output.right pinBus D input.left [15:0] pinBus DOUTBDOUT input.left [0:0] pinBus Q output.right [7:0] pinBus SR output.right [0:0] pinBus abs_b_reg[1][15]_0 input.left [15:0] pinBus out_data_reg[39]_0 output.right [39:0] pinBus wmem_raddr output.right [14:0] boxcolor 1 fillcolor 2 minwidth 13%
load symbol relu_activation work:relu_activation:NOFILE HIERBOX pin CLK input.left pin m_axis_tlast_OBUF output.right pin m_axis_tready_IBUF input.left pin m_axis_tvalid_OBUF output.right pin mac_out_ready output.right pin mac_out_valid input.left pin out_idx_reg[4] output.right pin out_valid_reg_reg_0 input.left pin p_0_in input.left pinBus D input.left [39:0] pinBus E output.right [0:0] pinBus Q input.left [6:0] pinBus SR input.left [0:0] pinBus out_data_reg_reg[39]_0 output.right [39:0] boxcolor 1 fillcolor 2 minwidth 13%
load symbol wmem_hidden work:wmem_hidden:NOFILE HIERBOX pin CLK input.left pin mem_reg_bram_0_0 input.left pin mem_reg_bram_10_0 input.left pin mem_reg_bram_10_1 input.left pin mem_reg_bram_11_0 input.left pin mem_reg_bram_11_1 input.left pin mem_reg_bram_12_0 input.left pin mem_reg_bram_13_0 input.left pin mem_reg_bram_13_1 input.left pin mem_reg_bram_1_0 input.left pin mem_reg_bram_1_1 input.left pin mem_reg_bram_2_0 input.left pin mem_reg_bram_2_1 input.left pin mem_reg_bram_3_0 input.left pin mem_reg_bram_3_1 input.left pin mem_reg_bram_4_0 input.left pin mem_reg_bram_4_1 input.left pin mem_reg_bram_5_0 input.left pin mem_reg_bram_5_1 input.left pin mem_reg_bram_6_0 input.left pin mem_reg_bram_6_1 input.left pin mem_reg_bram_7_0 input.left pin mem_reg_bram_7_1 input.left pin mem_reg_bram_8_0 input.left pin mem_reg_bram_9_0 input.left pin mem_reg_bram_9_1 input.left pin p_0_in input.left pin rst_n_IBUF input.left pin w_wr_en_IBUF input.left pinBus D input.left [15:0] pinBus DOUTBDOUT output.right [0:0] pinBus mem_reg_bram_14_0 output.right [15:0] pinBus w_addr_reg_reg[14]_0 input.left [14:0] pinBus wmem_raddr input.left [14:0] boxcolor 1 fillcolor 2 minwidth 13%
load symbol LUT3 hdi_primitives BOX pin O output.right pin I0 input.left pin I1 input.left pin I2 input.left fillcolor 1
load symbol FDRE hdi_primitives GEN pin Q output.right pin C input.clk.left pin CE input.left pin D input.left pin R input.left fillcolor 1
load port busy output -pg 1 -lvl 7 -x 5320 -y 700
load port clk input -pg 1 -lvl 0 -x 0 -y 3070
load port m_axis_tlast output -pg 1 -lvl 7 -x 5320 -y 1520
load port m_axis_tready input -pg 1 -lvl 0 -x 0 -y 1500
load port m_axis_tvalid output -pg 1 -lvl 7 -x 5320 -y 1310
load port rst_n input -pg 1 -lvl 0 -x 0 -y 2120
load port s_axis_tlast input -pg 1 -lvl 0 -x 0 -y 1640
load port s_axis_tready output -pg 1 -lvl 7 -x 5320 -y 1660
load port s_axis_tvalid input -pg 1 -lvl 0 -x 0 -y 1730
load port w_wr_en input -pg 1 -lvl 0 -x 0 -y 3140
load portBus m_axis_tdata output [39:0] -attr @name m_axis_tdata[39:0] -pg 1 -lvl 7 -x 5320 -y 1680
load portBus s_axis_tdata input [15:0] -attr @name s_axis_tdata[15:0] -pg 1 -lvl 0 -x 0 -y 60
load portBus w_addr_h input [6:0] -attr @name w_addr_h[6:0] -pg 1 -lvl 0 -x 0 -y 3240
load portBus w_addr_i input [7:0] -attr @name w_addr_i[7:0] -pg 1 -lvl 0 -x 0 -y 3870
load portBus w_data input [15:0] -attr @name w_data[15:0] -pg 1 -lvl 0 -x 0 -y 4590
load inst busy_OBUF_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 700
load inst clk_IBUF_BUFG_inst BUFGCE hdi_primitives -attr @cell(#000000) BUFGCE -pg 1 -lvl 2 -x 230 -y 3070
load inst clk_IBUF_inst IBUF {hdi_primitives:netlist:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 1 -x 50 -y 3060
load inst m_axis_tdata_OBUF[0]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1170
load inst m_axis_tdata_OBUF[10]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2080
load inst m_axis_tdata_OBUF[11]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2150
load inst m_axis_tdata_OBUF[12]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2220
load inst m_axis_tdata_OBUF[13]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2290
load inst m_axis_tdata_OBUF[14]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2360
load inst m_axis_tdata_OBUF[15]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2430
load inst m_axis_tdata_OBUF[16]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2500
load inst m_axis_tdata_OBUF[17]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2570
load inst m_axis_tdata_OBUF[18]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2640
load inst m_axis_tdata_OBUF[19]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2710
load inst m_axis_tdata_OBUF[1]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1240
load inst m_axis_tdata_OBUF[20]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2780
load inst m_axis_tdata_OBUF[21]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2850
load inst m_axis_tdata_OBUF[22]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2920
load inst m_axis_tdata_OBUF[23]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2990
load inst m_axis_tdata_OBUF[24]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3060
load inst m_axis_tdata_OBUF[25]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3130
load inst m_axis_tdata_OBUF[26]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3200
load inst m_axis_tdata_OBUF[27]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3270
load inst m_axis_tdata_OBUF[28]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3340
load inst m_axis_tdata_OBUF[29]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3410
load inst m_axis_tdata_OBUF[2]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1380
load inst m_axis_tdata_OBUF[30]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3480
load inst m_axis_tdata_OBUF[31]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3550
load inst m_axis_tdata_OBUF[32]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3620
load inst m_axis_tdata_OBUF[33]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3690
load inst m_axis_tdata_OBUF[34]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3760
load inst m_axis_tdata_OBUF[35]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3830
load inst m_axis_tdata_OBUF[36]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3900
load inst m_axis_tdata_OBUF[37]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 3970
load inst m_axis_tdata_OBUF[38]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 4040
load inst m_axis_tdata_OBUF[39]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 4110
load inst m_axis_tdata_OBUF[3]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1450
load inst m_axis_tdata_OBUF[4]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1590
load inst m_axis_tdata_OBUF[5]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1730
load inst m_axis_tdata_OBUF[6]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1800
load inst m_axis_tdata_OBUF[7]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1870
load inst m_axis_tdata_OBUF[8]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1940
load inst m_axis_tdata_OBUF[9]_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 2010
load inst m_axis_tlast_OBUF_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1520
load inst m_axis_tready_IBUF_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1490
load inst m_axis_tvalid_OBUF_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1310
load inst out_idx[0]_i_1 LUT1 hdi_primitives -attr @cell(#000000) LUT1 -pg 1 -lvl 2 -x 230 -y 1990
load inst out_idx[1]_i_1 LUT4 hdi_primitives -attr @cell(#000000) LUT4 -pg 1 -lvl 2 -x 230 -y 2220
load inst out_idx[2]_i_1 LUT5 hdi_primitives -attr @cell(#000000) LUT5 -pg 1 -lvl 2 -x 230 -y 2350
load inst out_idx[3]_i_1 LUT4 hdi_primitives -attr @cell(#000000) LUT4 -pg 1 -lvl 2 -x 230 -y 2500
load inst out_idx[4]_i_1 LUT5 hdi_primitives -attr @cell(#000000) LUT5 -pg 1 -lvl 2 -x 230 -y 2630
load inst out_idx[5]_i_1 LUT6 hdi_primitives -attr @cell(#000000) LUT6 -pg 1 -lvl 2 -x 230 -y 2780
load inst out_idx[6]_i_2 LUT2 hdi_primitives -attr @cell(#000000) LUT2 -pg 1 -lvl 2 -x 230 -y 2950
load inst out_idx_reg[0] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 1990
load inst out_idx_reg[1] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 2240
load inst out_idx_reg[2] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 2390
load inst out_idx_reg[3] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 2540
load inst out_idx_reg[4] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 2700
load inst out_idx_reg[5] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 2850
load inst out_idx_reg[6] FDRE hdi_primitivesR,_INVPIN_ -attr @cell(#000000) FDRE -pg 1 -lvl 3 -x 590 -y 3000
load inst rst_n_IBUF_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 2110
load inst s_axis_tdata_IBUF[0]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 50
load inst s_axis_tdata_IBUF[10]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 950
load inst s_axis_tdata_IBUF[11]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1040
load inst s_axis_tdata_IBUF[12]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1130
load inst s_axis_tdata_IBUF[13]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1220
load inst s_axis_tdata_IBUF[14]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1310
load inst s_axis_tdata_IBUF[15]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1400
load inst s_axis_tdata_IBUF[1]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 140
load inst s_axis_tdata_IBUF[2]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 230
load inst s_axis_tdata_IBUF[3]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 320
load inst s_axis_tdata_IBUF[4]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 410
load inst s_axis_tdata_IBUF[5]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 500
load inst s_axis_tdata_IBUF[6]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 590
load inst s_axis_tdata_IBUF[7]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 680
load inst s_axis_tdata_IBUF[8]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 770
load inst s_axis_tdata_IBUF[9]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 860
load inst s_axis_tlast_IBUF_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1630
load inst s_axis_tready_OBUF_inst OBUF hdi_primitives -attr @cell(#000000) OBUF -pg 1 -lvl 6 -x 5070 -y 1660
load inst s_axis_tvalid_IBUF_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 1720
load inst u_input_buffer input_buffer work:input_buffer:NOFILE -autohide -attr @cell(#000000) input_buffer -pinBusAttr D @name D[15:0] -pinBusAttr Q @name Q[7:0] -pinBusAttr inbuf_reg[255][15]_0 @name inbuf_reg[255][15]_0[15:0] -pg 1 -lvl 4 -x 1610 -y 930
load inst u_mac_engine mac_engine work:mac_engine:NOFILE -autohide -attr @cell(#000000) mac_engine -pinBusAttr D @name D[15:0] -pinBusAttr DOUTBDOUT @name DOUTBDOUT -pinBusAttr Q @name Q[7:0] -pinBusAttr SR @name SR -pinBusAttr abs_b_reg[1][15]_0 @name abs_b_reg[1][15]_0[15:0] -pinBusAttr out_data_reg[39]_0 @name out_data_reg[39]_0[39:0] -pinBusAttr wmem_raddr @name wmem_raddr[14:0] -pg 1 -lvl 5 -x 3360 -y 50
load inst u_relu_activation relu_activation work:relu_activation:NOFILE -fold -autohide -attr @cell(#000000) relu_activation -attr @fillcolor #dfebf8 -pinBusAttr D @name D[39:0] -pinBusAttr E @name E -pinBusAttr Q @name Q[6:0] -pinBusAttr SR @name SR -pinBusAttr out_data_reg_reg[39]_0 @name out_data_reg_reg[39]_0[39:0] -pg 1 -lvl 4 -x 1610 -y 570
load inst u_wmem_hidden wmem_hidden work:wmem_hidden:NOFILE -autohide -attr @cell(#000000) wmem_hidden -pinBusAttr D @name D[15:0] -pinBusAttr DOUTBDOUT @name DOUTBDOUT -pinBusAttr mem_reg_bram_14_0 @name mem_reg_bram_14_0[15:0] -pinBusAttr w_addr_reg_reg[14]_0 @name w_addr_reg_reg[14]_0[14:0] -pinBusAttr wmem_raddr @name wmem_raddr[14:0] -pg 1 -lvl 4 -x 1610 -y 2530
load inst w_addr_h_IBUF[0]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3230
load inst w_addr_h_IBUF[1]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3320
load inst w_addr_h_IBUF[2]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3410
load inst w_addr_h_IBUF[3]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3500
load inst w_addr_h_IBUF[4]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3590
load inst w_addr_h_IBUF[5]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3680
load inst w_addr_h_IBUF[6]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3770
load inst w_addr_i_IBUF[0]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3860
load inst w_addr_i_IBUF[1]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3950
load inst w_addr_i_IBUF[2]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4040
load inst w_addr_i_IBUF[3]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4130
load inst w_addr_i_IBUF[4]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4220
load inst w_addr_i_IBUF[5]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4310
load inst w_addr_i_IBUF[6]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4400
load inst w_addr_i_IBUF[7]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4490
load inst w_data_IBUF[0]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4580
load inst w_data_IBUF[10]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5480
load inst w_data_IBUF[11]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5570
load inst w_data_IBUF[12]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5660
load inst w_data_IBUF[13]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5750
load inst w_data_IBUF[14]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5840
load inst w_data_IBUF[15]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5930
load inst w_data_IBUF[1]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4670
load inst w_data_IBUF[2]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4760
load inst w_data_IBUF[3]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4850
load inst w_data_IBUF[4]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 4940
load inst w_data_IBUF[5]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5030
load inst w_data_IBUF[6]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5120
load inst w_data_IBUF[7]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5210
load inst w_data_IBUF[8]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5300
load inst w_data_IBUF[9]_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 5390
load inst w_wr_en_IBUF_inst IBUF {hdi_primitives:abstract:no file specified} -autohide -attr @cell(#000000) IBUF -pg 1 -lvl 3 -x 590 -y 3130
load inst u_relu_activation|m_axis_tlast_OBUF_inst_i_1 LUT3 hdi_primitives -hier u_relu_activation -attr @cell(#000000) LUT3 -attr @name m_axis_tlast_OBUF_inst_i_1 -pg 1 -lvl 2 -x 2130 -y 6578
load inst u_relu_activation|m_axis_tlast_OBUF_inst_i_2 LUT6 hdi_primitives -hier u_relu_activation -attr @cell(#000000) LUT6 -attr @name m_axis_tlast_OBUF_inst_i_2 -pg 1 -lvl 1 -x 1770 -y 6428
load inst u_relu_activation|out_data_reg[39]_i_2 LUT3 hdi_primitives -hier u_relu_activation -attr @cell(#000000) LUT3 -attr @name out_data_reg[39]_i_2 -pg 1 -lvl 1 -x 1770 -y 6648
load inst u_relu_activation|out_data_reg_reg[0] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[0] -pg 1 -lvl 2 -x 2130 -y 628
load inst u_relu_activation|out_data_reg_reg[10] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[10] -pg 1 -lvl 2 -x 2130 -y 2128
load inst u_relu_activation|out_data_reg_reg[11] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[11] -pg 1 -lvl 2 -x 2130 -y 2278
load inst u_relu_activation|out_data_reg_reg[12] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[12] -pg 1 -lvl 2 -x 2130 -y 2428
load inst u_relu_activation|out_data_reg_reg[13] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[13] -pg 1 -lvl 2 -x 2130 -y 2578
load inst u_relu_activation|out_data_reg_reg[14] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[14] -pg 1 -lvl 2 -x 2130 -y 2728
load inst u_relu_activation|out_data_reg_reg[15] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[15] -pg 1 -lvl 2 -x 2130 -y 2878
load inst u_relu_activation|out_data_reg_reg[16] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[16] -pg 1 -lvl 2 -x 2130 -y 3028
load inst u_relu_activation|out_data_reg_reg[17] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[17] -pg 1 -lvl 2 -x 2130 -y 3178
load inst u_relu_activation|out_data_reg_reg[18] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[18] -pg 1 -lvl 2 -x 2130 -y 3328
load inst u_relu_activation|out_data_reg_reg[19] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[19] -pg 1 -lvl 2 -x 2130 -y 3478
load inst u_relu_activation|out_data_reg_reg[1] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[1] -pg 1 -lvl 2 -x 2130 -y 778
load inst u_relu_activation|out_data_reg_reg[20] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[20] -pg 1 -lvl 2 -x 2130 -y 3628
load inst u_relu_activation|out_data_reg_reg[21] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[21] -pg 1 -lvl 2 -x 2130 -y 3778
load inst u_relu_activation|out_data_reg_reg[22] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[22] -pg 1 -lvl 2 -x 2130 -y 3928
load inst u_relu_activation|out_data_reg_reg[23] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[23] -pg 1 -lvl 2 -x 2130 -y 4078
load inst u_relu_activation|out_data_reg_reg[24] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[24] -pg 1 -lvl 2 -x 2130 -y 4228
load inst u_relu_activation|out_data_reg_reg[25] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[25] -pg 1 -lvl 2 -x 2130 -y 4378
load inst u_relu_activation|out_data_reg_reg[26] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[26] -pg 1 -lvl 2 -x 2130 -y 4528
load inst u_relu_activation|out_data_reg_reg[27] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[27] -pg 1 -lvl 2 -x 2130 -y 4678
load inst u_relu_activation|out_data_reg_reg[28] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[28] -pg 1 -lvl 2 -x 2130 -y 4828
load inst u_relu_activation|out_data_reg_reg[29] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[29] -pg 1 -lvl 2 -x 2130 -y 4978
load inst u_relu_activation|out_data_reg_reg[2] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[2] -pg 1 -lvl 2 -x 2130 -y 928
load inst u_relu_activation|out_data_reg_reg[30] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[30] -pg 1 -lvl 2 -x 2130 -y 5128
load inst u_relu_activation|out_data_reg_reg[31] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[31] -pg 1 -lvl 2 -x 2130 -y 5278
load inst u_relu_activation|out_data_reg_reg[32] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[32] -pg 1 -lvl 2 -x 2130 -y 5428
load inst u_relu_activation|out_data_reg_reg[33] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[33] -pg 1 -lvl 2 -x 2130 -y 5578
load inst u_relu_activation|out_data_reg_reg[34] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[34] -pg 1 -lvl 2 -x 2130 -y 5728
load inst u_relu_activation|out_data_reg_reg[35] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[35] -pg 1 -lvl 2 -x 2130 -y 5878
load inst u_relu_activation|out_data_reg_reg[36] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[36] -pg 1 -lvl 2 -x 2130 -y 6028
load inst u_relu_activation|out_data_reg_reg[37] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[37] -pg 1 -lvl 2 -x 2130 -y 6178
load inst u_relu_activation|out_data_reg_reg[38] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[38] -pg 1 -lvl 2 -x 2130 -y 6328
load inst u_relu_activation|out_data_reg_reg[39] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[39] -pg 1 -lvl 2 -x 2130 -y 6478
load inst u_relu_activation|out_data_reg_reg[3] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[3] -pg 1 -lvl 2 -x 2130 -y 1078
load inst u_relu_activation|out_data_reg_reg[4] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[4] -pg 1 -lvl 2 -x 2130 -y 1228
load inst u_relu_activation|out_data_reg_reg[5] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[5] -pg 1 -lvl 2 -x 2130 -y 1378
load inst u_relu_activation|out_data_reg_reg[6] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[6] -pg 1 -lvl 2 -x 2130 -y 1528
load inst u_relu_activation|out_data_reg_reg[7] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[7] -pg 1 -lvl 2 -x 2130 -y 1678
load inst u_relu_activation|out_data_reg_reg[8] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[8] -pg 1 -lvl 2 -x 2130 -y 1828
load inst u_relu_activation|out_data_reg_reg[9] FDRE hdi_primitives -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_data_reg_reg[9] -pg 1 -lvl 2 -x 2130 -y 1978
load inst u_relu_activation|out_idx[6]_i_1 LUT2 hdi_primitives -hier u_relu_activation -attr @cell(#000000) LUT2 -attr @name out_idx[6]_i_1 -pg 1 -lvl 2 -x 2130 -y 6718
load inst u_relu_activation|out_index[7]_i_3 LUT2 hdi_primitives -hier u_relu_activation -attr @cell(#000000) LUT2 -attr @name out_index[7]_i_3 -pg 1 -lvl 2 -x 2130 -y 6808
load inst u_relu_activation|out_valid_reg_reg FDRE hdi_primitivesR,_INVPIN_ -hier u_relu_activation -attr @cell(#000000) FDRE -attr @name out_valid_reg_reg -pg 1 -lvl 1 -x 1770 -y 6838
load net VCC_1 -power -pin clk_IBUF_BUFG_inst CE
load net busy -port busy -pin busy_OBUF_inst O
netloc busy 1 6 1 NJ 700
load net busy_OBUF -pin u_input_buffer busy_OBUF -pin u_mac_engine busy_OBUF
netloc busy_OBUF 1 3 3 1420 880 1930J 1700 4610
load net clk -port clk -pin clk_IBUF_inst I
netloc clk 1 0 1 NJ 3070
load net clk_IBUF -pin clk_IBUF_BUFG_inst I -pin clk_IBUF_inst O
netloc clk_IBUF 1 1 1 NJ 3070
load net clk_IBUF_BUFG -pin clk_IBUF_BUFG_inst O -pin out_idx_reg[0] C -pin out_idx_reg[1] C -pin out_idx_reg[2] C -pin out_idx_reg[3] C -pin out_idx_reg[4] C -pin out_idx_reg[5] C -pin out_idx_reg[6] C -pin u_input_buffer clk_IBUF_BUFG -pin u_mac_engine clk_IBUF_BUFG -pin u_relu_activation CLK -pin u_wmem_hidden CLK
netloc clk_IBUF_BUFG 1 2 3 440 1910 900 320 3190J
load net lopt -pin busy_OBUF_inst I -pin u_mac_engine lopt
netloc lopt 1 5 1 NJ 700
load net m_axis_tdata[0] -attr @rip(#000000) 0 -port m_axis_tdata[0] -pin m_axis_tdata_OBUF[0]_inst O
load net m_axis_tdata[10] -attr @rip(#000000) 10 -port m_axis_tdata[10] -pin m_axis_tdata_OBUF[10]_inst O
load net m_axis_tdata[11] -attr @rip(#000000) 11 -port m_axis_tdata[11] -pin m_axis_tdata_OBUF[11]_inst O
load net m_axis_tdata[12] -attr @rip(#000000) 12 -port m_axis_tdata[12] -pin m_axis_tdata_OBUF[12]_inst O
load net m_axis_tdata[13] -attr @rip(#000000) 13 -port m_axis_tdata[13] -pin m_axis_tdata_OBUF[13]_inst O
load net m_axis_tdata[14] -attr @rip(#000000) 14 -port m_axis_tdata[14] -pin m_axis_tdata_OBUF[14]_inst O
load net m_axis_tdata[15] -attr @rip(#000000) 15 -port m_axis_tdata[15] -pin m_axis_tdata_OBUF[15]_inst O
load net m_axis_tdata[16] -attr @rip(#000000) 16 -port m_axis_tdata[16] -pin m_axis_tdata_OBUF[16]_inst O
load net m_axis_tdata[17] -attr @rip(#000000) 17 -port m_axis_tdata[17] -pin m_axis_tdata_OBUF[17]_inst O
load net m_axis_tdata[18] -attr @rip(#000000) 18 -port m_axis_tdata[18] -pin m_axis_tdata_OBUF[18]_inst O
load net m_axis_tdata[19] -attr @rip(#000000) 19 -port m_axis_tdata[19] -pin m_axis_tdata_OBUF[19]_inst O
load net m_axis_tdata[1] -attr @rip(#000000) 1 -port m_axis_tdata[1] -pin m_axis_tdata_OBUF[1]_inst O
load net m_axis_tdata[20] -attr @rip(#000000) 20 -port m_axis_tdata[20] -pin m_axis_tdata_OBUF[20]_inst O
load net m_axis_tdata[21] -attr @rip(#000000) 21 -port m_axis_tdata[21] -pin m_axis_tdata_OBUF[21]_inst O
load net m_axis_tdata[22] -attr @rip(#000000) 22 -port m_axis_tdata[22] -pin m_axis_tdata_OBUF[22]_inst O
load net m_axis_tdata[23] -attr @rip(#000000) 23 -port m_axis_tdata[23] -pin m_axis_tdata_OBUF[23]_inst O
load net m_axis_tdata[24] -attr @rip(#000000) 24 -port m_axis_tdata[24] -pin m_axis_tdata_OBUF[24]_inst O
load net m_axis_tdata[25] -attr @rip(#000000) 25 -port m_axis_tdata[25] -pin m_axis_tdata_OBUF[25]_inst O
load net m_axis_tdata[26] -attr @rip(#000000) 26 -port m_axis_tdata[26] -pin m_axis_tdata_OBUF[26]_inst O
load net m_axis_tdata[27] -attr @rip(#000000) 27 -port m_axis_tdata[27] -pin m_axis_tdata_OBUF[27]_inst O
load net m_axis_tdata[28] -attr @rip(#000000) 28 -port m_axis_tdata[28] -pin m_axis_tdata_OBUF[28]_inst O
load net m_axis_tdata[29] -attr @rip(#000000) 29 -port m_axis_tdata[29] -pin m_axis_tdata_OBUF[29]_inst O
load net m_axis_tdata[2] -attr @rip(#000000) 2 -port m_axis_tdata[2] -pin m_axis_tdata_OBUF[2]_inst O
load net m_axis_tdata[30] -attr @rip(#000000) 30 -port m_axis_tdata[30] -pin m_axis_tdata_OBUF[30]_inst O
load net m_axis_tdata[31] -attr @rip(#000000) 31 -port m_axis_tdata[31] -pin m_axis_tdata_OBUF[31]_inst O
load net m_axis_tdata[32] -attr @rip(#000000) 32 -port m_axis_tdata[32] -pin m_axis_tdata_OBUF[32]_inst O
load net m_axis_tdata[33] -attr @rip(#000000) 33 -port m_axis_tdata[33] -pin m_axis_tdata_OBUF[33]_inst O
load net m_axis_tdata[34] -attr @rip(#000000) 34 -port m_axis_tdata[34] -pin m_axis_tdata_OBUF[34]_inst O
load net m_axis_tdata[35] -attr @rip(#000000) 35 -port m_axis_tdata[35] -pin m_axis_tdata_OBUF[35]_inst O
load net m_axis_tdata[36] -attr @rip(#000000) 36 -port m_axis_tdata[36] -pin m_axis_tdata_OBUF[36]_inst O
load net m_axis_tdata[37] -attr @rip(#000000) 37 -port m_axis_tdata[37] -pin m_axis_tdata_OBUF[37]_inst O
load net m_axis_tdata[38] -attr @rip(#000000) 38 -port m_axis_tdata[38] -pin m_axis_tdata_OBUF[38]_inst O
load net m_axis_tdata[39] -attr @rip(#000000) 39 -port m_axis_tdata[39] -pin m_axis_tdata_OBUF[39]_inst O
load net m_axis_tdata[3] -attr @rip(#000000) 3 -port m_axis_tdata[3] -pin m_axis_tdata_OBUF[3]_inst O
load net m_axis_tdata[4] -attr @rip(#000000) 4 -port m_axis_tdata[4] -pin m_axis_tdata_OBUF[4]_inst O
load net m_axis_tdata[5] -attr @rip(#000000) 5 -port m_axis_tdata[5] -pin m_axis_tdata_OBUF[5]_inst O
load net m_axis_tdata[6] -attr @rip(#000000) 6 -port m_axis_tdata[6] -pin m_axis_tdata_OBUF[6]_inst O
load net m_axis_tdata[7] -attr @rip(#000000) 7 -port m_axis_tdata[7] -pin m_axis_tdata_OBUF[7]_inst O
load net m_axis_tdata[8] -attr @rip(#000000) 8 -port m_axis_tdata[8] -pin m_axis_tdata_OBUF[8]_inst O
load net m_axis_tdata[9] -attr @rip(#000000) 9 -port m_axis_tdata[9] -pin m_axis_tdata_OBUF[9]_inst O
load net m_axis_tdata_OBUF[0] -attr @rip(#000000) out_data_reg_reg[39]_0[0] -pin m_axis_tdata_OBUF[0]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[0]
load net m_axis_tdata_OBUF[10] -attr @rip(#000000) out_data_reg_reg[39]_0[10] -pin m_axis_tdata_OBUF[10]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[10]
load net m_axis_tdata_OBUF[11] -attr @rip(#000000) out_data_reg_reg[39]_0[11] -pin m_axis_tdata_OBUF[11]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[11]
load net m_axis_tdata_OBUF[12] -attr @rip(#000000) out_data_reg_reg[39]_0[12] -pin m_axis_tdata_OBUF[12]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[12]
load net m_axis_tdata_OBUF[13] -attr @rip(#000000) out_data_reg_reg[39]_0[13] -pin m_axis_tdata_OBUF[13]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[13]
load net m_axis_tdata_OBUF[14] -attr @rip(#000000) out_data_reg_reg[39]_0[14] -pin m_axis_tdata_OBUF[14]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[14]
load net m_axis_tdata_OBUF[15] -attr @rip(#000000) out_data_reg_reg[39]_0[15] -pin m_axis_tdata_OBUF[15]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[15]
load net m_axis_tdata_OBUF[16] -attr @rip(#000000) out_data_reg_reg[39]_0[16] -pin m_axis_tdata_OBUF[16]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[16]
load net m_axis_tdata_OBUF[17] -attr @rip(#000000) out_data_reg_reg[39]_0[17] -pin m_axis_tdata_OBUF[17]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[17]
load net m_axis_tdata_OBUF[18] -attr @rip(#000000) out_data_reg_reg[39]_0[18] -pin m_axis_tdata_OBUF[18]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[18]
load net m_axis_tdata_OBUF[19] -attr @rip(#000000) out_data_reg_reg[39]_0[19] -pin m_axis_tdata_OBUF[19]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[19]
load net m_axis_tdata_OBUF[1] -attr @rip(#000000) out_data_reg_reg[39]_0[1] -pin m_axis_tdata_OBUF[1]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[1]
load net m_axis_tdata_OBUF[20] -attr @rip(#000000) out_data_reg_reg[39]_0[20] -pin m_axis_tdata_OBUF[20]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[20]
load net m_axis_tdata_OBUF[21] -attr @rip(#000000) out_data_reg_reg[39]_0[21] -pin m_axis_tdata_OBUF[21]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[21]
load net m_axis_tdata_OBUF[22] -attr @rip(#000000) out_data_reg_reg[39]_0[22] -pin m_axis_tdata_OBUF[22]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[22]
load net m_axis_tdata_OBUF[23] -attr @rip(#000000) out_data_reg_reg[39]_0[23] -pin m_axis_tdata_OBUF[23]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[23]
load net m_axis_tdata_OBUF[24] -attr @rip(#000000) out_data_reg_reg[39]_0[24] -pin m_axis_tdata_OBUF[24]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[24]
load net m_axis_tdata_OBUF[25] -attr @rip(#000000) out_data_reg_reg[39]_0[25] -pin m_axis_tdata_OBUF[25]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[25]
load net m_axis_tdata_OBUF[26] -attr @rip(#000000) out_data_reg_reg[39]_0[26] -pin m_axis_tdata_OBUF[26]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[26]
load net m_axis_tdata_OBUF[27] -attr @rip(#000000) out_data_reg_reg[39]_0[27] -pin m_axis_tdata_OBUF[27]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[27]
load net m_axis_tdata_OBUF[28] -attr @rip(#000000) out_data_reg_reg[39]_0[28] -pin m_axis_tdata_OBUF[28]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[28]
load net m_axis_tdata_OBUF[29] -attr @rip(#000000) out_data_reg_reg[39]_0[29] -pin m_axis_tdata_OBUF[29]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[29]
load net m_axis_tdata_OBUF[2] -attr @rip(#000000) out_data_reg_reg[39]_0[2] -pin m_axis_tdata_OBUF[2]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[2]
load net m_axis_tdata_OBUF[30] -attr @rip(#000000) out_data_reg_reg[39]_0[30] -pin m_axis_tdata_OBUF[30]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[30]
load net m_axis_tdata_OBUF[31] -attr @rip(#000000) out_data_reg_reg[39]_0[31] -pin m_axis_tdata_OBUF[31]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[31]
load net m_axis_tdata_OBUF[32] -attr @rip(#000000) out_data_reg_reg[39]_0[32] -pin m_axis_tdata_OBUF[32]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[32]
load net m_axis_tdata_OBUF[33] -attr @rip(#000000) out_data_reg_reg[39]_0[33] -pin m_axis_tdata_OBUF[33]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[33]
load net m_axis_tdata_OBUF[34] -attr @rip(#000000) out_data_reg_reg[39]_0[34] -pin m_axis_tdata_OBUF[34]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[34]
load net m_axis_tdata_OBUF[35] -attr @rip(#000000) out_data_reg_reg[39]_0[35] -pin m_axis_tdata_OBUF[35]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[35]
load net m_axis_tdata_OBUF[36] -attr @rip(#000000) out_data_reg_reg[39]_0[36] -pin m_axis_tdata_OBUF[36]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[36]
load net m_axis_tdata_OBUF[37] -attr @rip(#000000) out_data_reg_reg[39]_0[37] -pin m_axis_tdata_OBUF[37]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[37]
load net m_axis_tdata_OBUF[38] -attr @rip(#000000) out_data_reg_reg[39]_0[38] -pin m_axis_tdata_OBUF[38]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[38]
load net m_axis_tdata_OBUF[39] -attr @rip(#000000) out_data_reg_reg[39]_0[39] -pin m_axis_tdata_OBUF[39]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[39]
load net m_axis_tdata_OBUF[3] -attr @rip(#000000) out_data_reg_reg[39]_0[3] -pin m_axis_tdata_OBUF[3]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[3]
load net m_axis_tdata_OBUF[4] -attr @rip(#000000) out_data_reg_reg[39]_0[4] -pin m_axis_tdata_OBUF[4]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[4]
load net m_axis_tdata_OBUF[5] -attr @rip(#000000) out_data_reg_reg[39]_0[5] -pin m_axis_tdata_OBUF[5]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[5]
load net m_axis_tdata_OBUF[6] -attr @rip(#000000) out_data_reg_reg[39]_0[6] -pin m_axis_tdata_OBUF[6]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[6]
load net m_axis_tdata_OBUF[7] -attr @rip(#000000) out_data_reg_reg[39]_0[7] -pin m_axis_tdata_OBUF[7]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[7]
load net m_axis_tdata_OBUF[8] -attr @rip(#000000) out_data_reg_reg[39]_0[8] -pin m_axis_tdata_OBUF[8]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[8]
load net m_axis_tdata_OBUF[9] -attr @rip(#000000) out_data_reg_reg[39]_0[9] -pin m_axis_tdata_OBUF[9]_inst I -pin u_relu_activation out_data_reg_reg[39]_0[9]
load net m_axis_tlast -port m_axis_tlast -pin m_axis_tlast_OBUF_inst O
netloc m_axis_tlast 1 6 1 NJ 1520
load net m_axis_tlast_OBUF -pin m_axis_tlast_OBUF_inst I -pin u_relu_activation m_axis_tlast_OBUF
netloc m_axis_tlast_OBUF 1 4 2 2890J 1520 NJ
load net m_axis_tready -port m_axis_tready -pin m_axis_tready_IBUF_inst I
netloc m_axis_tready 1 0 3 NJ 1500 NJ 1500 NJ
load net m_axis_tready_IBUF -pin m_axis_tready_IBUF_inst O -pin u_mac_engine m_axis_tready_IBUF -pin u_relu_activation m_axis_tready_IBUF
netloc m_axis_tready_IBUF 1 3 2 780 340 3170J
load net m_axis_tvalid -port m_axis_tvalid -pin m_axis_tvalid_OBUF_inst O
netloc m_axis_tvalid 1 6 1 NJ 1310
load net m_axis_tvalid_OBUF -pin m_axis_tvalid_OBUF_inst I -pin u_mac_engine m_axis_tvalid_OBUF -pin u_relu_activation m_axis_tvalid_OBUF
netloc m_axis_tvalid_OBUF 1 4 2 2870 1500 5030J
load net mac_out_data[0] -attr @rip(#000000) out_data_reg[39]_0[0] -pin u_mac_engine out_data_reg[39]_0[0] -pin u_relu_activation D[0]
load net mac_out_data[10] -attr @rip(#000000) out_data_reg[39]_0[10] -pin u_mac_engine out_data_reg[39]_0[10] -pin u_relu_activation D[10]
load net mac_out_data[11] -attr @rip(#000000) out_data_reg[39]_0[11] -pin u_mac_engine out_data_reg[39]_0[11] -pin u_relu_activation D[11]
load net mac_out_data[12] -attr @rip(#000000) out_data_reg[39]_0[12] -pin u_mac_engine out_data_reg[39]_0[12] -pin u_relu_activation D[12]
load net mac_out_data[13] -attr @rip(#000000) out_data_reg[39]_0[13] -pin u_mac_engine out_data_reg[39]_0[13] -pin u_relu_activation D[13]
load net mac_out_data[14] -attr @rip(#000000) out_data_reg[39]_0[14] -pin u_mac_engine out_data_reg[39]_0[14] -pin u_relu_activation D[14]
load net mac_out_data[15] -attr @rip(#000000) out_data_reg[39]_0[15] -pin u_mac_engine out_data_reg[39]_0[15] -pin u_relu_activation D[15]
load net mac_out_data[16] -attr @rip(#000000) out_data_reg[39]_0[16] -pin u_mac_engine out_data_reg[39]_0[16] -pin u_relu_activation D[16]
load net mac_out_data[17] -attr @rip(#000000) out_data_reg[39]_0[17] -pin u_mac_engine out_data_reg[39]_0[17] -pin u_relu_activation D[17]
load net mac_out_data[18] -attr @rip(#000000) out_data_reg[39]_0[18] -pin u_mac_engine out_data_reg[39]_0[18] -pin u_relu_activation D[18]
load net mac_out_data[19] -attr @rip(#000000) out_data_reg[39]_0[19] -pin u_mac_engine out_data_reg[39]_0[19] -pin u_relu_activation D[19]
load net mac_out_data[1] -attr @rip(#000000) out_data_reg[39]_0[1] -pin u_mac_engine out_data_reg[39]_0[1] -pin u_relu_activation D[1]
load net mac_out_data[20] -attr @rip(#000000) out_data_reg[39]_0[20] -pin u_mac_engine out_data_reg[39]_0[20] -pin u_relu_activation D[20]
load net mac_out_data[21] -attr @rip(#000000) out_data_reg[39]_0[21] -pin u_mac_engine out_data_reg[39]_0[21] -pin u_relu_activation D[21]
load net mac_out_data[22] -attr @rip(#000000) out_data_reg[39]_0[22] -pin u_mac_engine out_data_reg[39]_0[22] -pin u_relu_activation D[22]
load net mac_out_data[23] -attr @rip(#000000) out_data_reg[39]_0[23] -pin u_mac_engine out_data_reg[39]_0[23] -pin u_relu_activation D[23]
load net mac_out_data[24] -attr @rip(#000000) out_data_reg[39]_0[24] -pin u_mac_engine out_data_reg[39]_0[24] -pin u_relu_activation D[24]
load net mac_out_data[25] -attr @rip(#000000) out_data_reg[39]_0[25] -pin u_mac_engine out_data_reg[39]_0[25] -pin u_relu_activation D[25]
load net mac_out_data[26] -attr @rip(#000000) out_data_reg[39]_0[26] -pin u_mac_engine out_data_reg[39]_0[26] -pin u_relu_activation D[26]
load net mac_out_data[27] -attr @rip(#000000) out_data_reg[39]_0[27] -pin u_mac_engine out_data_reg[39]_0[27] -pin u_relu_activation D[27]
load net mac_out_data[28] -attr @rip(#000000) out_data_reg[39]_0[28] -pin u_mac_engine out_data_reg[39]_0[28] -pin u_relu_activation D[28]
load net mac_out_data[29] -attr @rip(#000000) out_data_reg[39]_0[29] -pin u_mac_engine out_data_reg[39]_0[29] -pin u_relu_activation D[29]
load net mac_out_data[2] -attr @rip(#000000) out_data_reg[39]_0[2] -pin u_mac_engine out_data_reg[39]_0[2] -pin u_relu_activation D[2]
load net mac_out_data[30] -attr @rip(#000000) out_data_reg[39]_0[30] -pin u_mac_engine out_data_reg[39]_0[30] -pin u_relu_activation D[30]
load net mac_out_data[31] -attr @rip(#000000) out_data_reg[39]_0[31] -pin u_mac_engine out_data_reg[39]_0[31] -pin u_relu_activation D[31]
load net mac_out_data[32] -attr @rip(#000000) out_data_reg[39]_0[32] -pin u_mac_engine out_data_reg[39]_0[32] -pin u_relu_activation D[32]
load net mac_out_data[33] -attr @rip(#000000) out_data_reg[39]_0[33] -pin u_mac_engine out_data_reg[39]_0[33] -pin u_relu_activation D[33]
load net mac_out_data[34] -attr @rip(#000000) out_data_reg[39]_0[34] -pin u_mac_engine out_data_reg[39]_0[34] -pin u_relu_activation D[34]
load net mac_out_data[35] -attr @rip(#000000) out_data_reg[39]_0[35] -pin u_mac_engine out_data_reg[39]_0[35] -pin u_relu_activation D[35]
load net mac_out_data[36] -attr @rip(#000000) out_data_reg[39]_0[36] -pin u_mac_engine out_data_reg[39]_0[36] -pin u_relu_activation D[36]
load net mac_out_data[37] -attr @rip(#000000) out_data_reg[39]_0[37] -pin u_mac_engine out_data_reg[39]_0[37] -pin u_relu_activation D[37]
load net mac_out_data[38] -attr @rip(#000000) out_data_reg[39]_0[38] -pin u_mac_engine out_data_reg[39]_0[38] -pin u_relu_activation D[38]
load net mac_out_data[39] -attr @rip(#000000) out_data_reg[39]_0[39] -pin u_mac_engine out_data_reg[39]_0[39] -pin u_relu_activation D[39]
load net mac_out_data[3] -attr @rip(#000000) out_data_reg[39]_0[3] -pin u_mac_engine out_data_reg[39]_0[3] -pin u_relu_activation D[3]
load net mac_out_data[4] -attr @rip(#000000) out_data_reg[39]_0[4] -pin u_mac_engine out_data_reg[39]_0[4] -pin u_relu_activation D[4]
load net mac_out_data[5] -attr @rip(#000000) out_data_reg[39]_0[5] -pin u_mac_engine out_data_reg[39]_0[5] -pin u_relu_activation D[5]
load net mac_out_data[6] -attr @rip(#000000) out_data_reg[39]_0[6] -pin u_mac_engine out_data_reg[39]_0[6] -pin u_relu_activation D[6]
load net mac_out_data[7] -attr @rip(#000000) out_data_reg[39]_0[7] -pin u_mac_engine out_data_reg[39]_0[7] -pin u_relu_activation D[7]
load net mac_out_data[8] -attr @rip(#000000) out_data_reg[39]_0[8] -pin u_mac_engine out_data_reg[39]_0[8] -pin u_relu_activation D[8]
load net mac_out_data[9] -attr @rip(#000000) out_data_reg[39]_0[9] -pin u_mac_engine out_data_reg[39]_0[9] -pin u_relu_activation D[9]
load net mac_out_ready -pin u_mac_engine mac_out_ready -pin u_relu_activation mac_out_ready
netloc mac_out_ready 1 4 1 3030 660n
load net mac_out_valid -pin u_mac_engine mac_out_valid -pin u_relu_activation mac_out_valid
netloc mac_out_valid 1 3 3 1340 500 2910J 1560 4130
load net out_idx0 -attr @rip(#000000) E[0] -pin out_idx_reg[0] CE -pin out_idx_reg[1] CE -pin out_idx_reg[2] CE -pin out_idx_reg[3] CE -pin out_idx_reg[4] CE -pin out_idx_reg[5] CE -pin out_idx_reg[6] CE -pin u_relu_activation E[0]
netloc out_idx0 1 2 3 500 2620 780J 3400 1910
load net out_idx[0] -attr @rip(#000000) 0 -pin out_idx[0]_i_1 I0 -pin out_idx[1]_i_1 I3 -pin out_idx[2]_i_1 I3 -pin out_idx[3]_i_1 I1 -pin out_idx[4]_i_1 I1 -pin out_idx[5]_i_1 I2 -pin out_idx_reg[0] Q -pin u_relu_activation Q[0]
load net out_idx[0]_i_1_n_0 -pin out_idx[0]_i_1 O -pin out_idx_reg[0] D
netloc out_idx[0]_i_1_n_0 1 2 1 N 2000
load net out_idx[1] -attr @rip(#000000) 1 -pin out_idx[1]_i_1 I2 -pin out_idx[2]_i_1 I4 -pin out_idx[3]_i_1 I0 -pin out_idx[4]_i_1 I2 -pin out_idx[5]_i_1 I1 -pin out_idx_reg[1] Q -pin u_relu_activation Q[1]
load net out_idx[1]_i_1_n_0 -pin out_idx[1]_i_1 O -pin out_idx_reg[1] D
netloc out_idx[1]_i_1_n_0 1 2 1 N 2250
load net out_idx[2] -attr @rip(#000000) 2 -pin out_idx[2]_i_1 I2 -pin out_idx[3]_i_1 I2 -pin out_idx[4]_i_1 I0 -pin out_idx[5]_i_1 I3 -pin out_idx_reg[2] Q -pin u_relu_activation Q[2]
load net out_idx[2]_i_1_n_0 -pin out_idx[2]_i_1 O -pin out_idx_reg[2] D
netloc out_idx[2]_i_1_n_0 1 2 1 N 2400
load net out_idx[3] -attr @rip(#000000) 3 -pin out_idx[3]_i_1 I3 -pin out_idx[4]_i_1 I3 -pin out_idx[5]_i_1 I0 -pin out_idx_reg[3] Q -pin u_relu_activation Q[3]
load net out_idx[3]_i_1_n_0 -pin out_idx[3]_i_1 O -pin out_idx_reg[3] D
netloc out_idx[3]_i_1_n_0 1 2 1 480 2530n
load net out_idx[4] -attr @rip(#000000) 4 -pin out_idx[4]_i_1 I4 -pin out_idx[5]_i_1 I4 -pin out_idx_reg[4] Q -pin u_relu_activation Q[4]
load net out_idx[4]_i_1_n_0 -pin out_idx[4]_i_1 O -pin out_idx_reg[4] D
netloc out_idx[4]_i_1_n_0 1 2 1 420 2680n
load net out_idx[5] -attr @rip(#000000) 5 -pin out_idx[5]_i_1 I5 -pin out_idx_reg[5] Q -pin u_relu_activation Q[5]
load net out_idx[5]_i_1_n_0 -pin out_idx[5]_i_1 O -pin out_idx_reg[5] D
netloc out_idx[5]_i_1_n_0 1 2 1 420 2830n
load net out_idx[6] -attr @rip(#000000) 6 -pin out_idx[1]_i_1 I0 -pin out_idx[2]_i_1 I0 -pin out_idx[6]_i_2 I0 -pin out_idx_reg[6] Q -pin u_relu_activation Q[6]
load net out_idx[6]_i_2_n_0 -pin out_idx[6]_i_2 O -pin out_idx_reg[6] D
netloc out_idx[6]_i_2_n_0 1 2 1 420 2960n
load net p_0_in -pin out_idx_reg[0] R -pin out_idx_reg[1] R -pin out_idx_reg[2] R -pin out_idx_reg[3] R -pin out_idx_reg[4] R -pin out_idx_reg[5] R -pin out_idx_reg[6] R -pin u_input_buffer p_0_in -pin u_mac_engine p_0_in -pin u_relu_activation p_0_in -pin u_wmem_hidden p_0_in
netloc p_0_in 1 2 4 460 2160 920 820 1990J 1620 3770
load net p_2_out[0] -attr @rip(#000000) mem_reg_bram_14_0[0] -pin u_mac_engine abs_b_reg[1][15]_0[0] -pin u_wmem_hidden mem_reg_bram_14_0[0]
load net p_2_out[10] -attr @rip(#000000) mem_reg_bram_14_0[10] -pin u_mac_engine abs_b_reg[1][15]_0[10] -pin u_wmem_hidden mem_reg_bram_14_0[10]
load net p_2_out[11] -attr @rip(#000000) mem_reg_bram_14_0[11] -pin u_mac_engine abs_b_reg[1][15]_0[11] -pin u_wmem_hidden mem_reg_bram_14_0[11]
load net p_2_out[12] -attr @rip(#000000) mem_reg_bram_14_0[12] -pin u_mac_engine abs_b_reg[1][15]_0[12] -pin u_wmem_hidden mem_reg_bram_14_0[12]
load net p_2_out[13] -attr @rip(#000000) mem_reg_bram_14_0[13] -pin u_mac_engine abs_b_reg[1][15]_0[13] -pin u_wmem_hidden mem_reg_bram_14_0[13]
load net p_2_out[14] -attr @rip(#000000) mem_reg_bram_14_0[14] -pin u_mac_engine abs_b_reg[1][15]_0[14] -pin u_wmem_hidden mem_reg_bram_14_0[14]
load net p_2_out[15] -attr @rip(#000000) mem_reg_bram_14_0[15] -pin u_mac_engine abs_b_reg[1][15]_0[15] -pin u_wmem_hidden mem_reg_bram_14_0[15]
load net p_2_out[1] -attr @rip(#000000) mem_reg_bram_14_0[1] -pin u_mac_engine abs_b_reg[1][15]_0[1] -pin u_wmem_hidden mem_reg_bram_14_0[1]
load net p_2_out[2] -attr @rip(#000000) mem_reg_bram_14_0[2] -pin u_mac_engine abs_b_reg[1][15]_0[2] -pin u_wmem_hidden mem_reg_bram_14_0[2]
load net p_2_out[3] -attr @rip(#000000) mem_reg_bram_14_0[3] -pin u_mac_engine abs_b_reg[1][15]_0[3] -pin u_wmem_hidden mem_reg_bram_14_0[3]
load net p_2_out[4] -attr @rip(#000000) mem_reg_bram_14_0[4] -pin u_mac_engine abs_b_reg[1][15]_0[4] -pin u_wmem_hidden mem_reg_bram_14_0[4]
load net p_2_out[5] -attr @rip(#000000) mem_reg_bram_14_0[5] -pin u_mac_engine abs_b_reg[1][15]_0[5] -pin u_wmem_hidden mem_reg_bram_14_0[5]
load net p_2_out[6] -attr @rip(#000000) mem_reg_bram_14_0[6] -pin u_mac_engine abs_b_reg[1][15]_0[6] -pin u_wmem_hidden mem_reg_bram_14_0[6]
load net p_2_out[7] -attr @rip(#000000) mem_reg_bram_14_0[7] -pin u_mac_engine abs_b_reg[1][15]_0[7] -pin u_wmem_hidden mem_reg_bram_14_0[7]
load net p_2_out[8] -attr @rip(#000000) mem_reg_bram_14_0[8] -pin u_mac_engine abs_b_reg[1][15]_0[8] -pin u_wmem_hidden mem_reg_bram_14_0[8]
load net p_2_out[9] -attr @rip(#000000) mem_reg_bram_14_0[9] -pin u_mac_engine abs_b_reg[1][15]_0[9] -pin u_wmem_hidden mem_reg_bram_14_0[9]
load net rst_n -port rst_n -pin rst_n_IBUF_inst I
netloc rst_n 1 0 3 NJ 2120 NJ 2120 NJ
load net rst_n_IBUF -pin rst_n_IBUF_inst O -pin u_input_buffer rst_n_IBUF -pin u_mac_engine rst_n_IBUF -pin u_wmem_hidden rst_n_IBUF
netloc rst_n_IBUF 1 3 2 940 760 2930J
load net s_axis_tdata[0] -attr @rip(#000000) s_axis_tdata[0] -port s_axis_tdata[0] -pin s_axis_tdata_IBUF[0]_inst I
load net s_axis_tdata[10] -attr @rip(#000000) s_axis_tdata[10] -port s_axis_tdata[10] -pin s_axis_tdata_IBUF[10]_inst I
load net s_axis_tdata[11] -attr @rip(#000000) s_axis_tdata[11] -port s_axis_tdata[11] -pin s_axis_tdata_IBUF[11]_inst I
load net s_axis_tdata[12] -attr @rip(#000000) s_axis_tdata[12] -port s_axis_tdata[12] -pin s_axis_tdata_IBUF[12]_inst I
load net s_axis_tdata[13] -attr @rip(#000000) s_axis_tdata[13] -port s_axis_tdata[13] -pin s_axis_tdata_IBUF[13]_inst I
load net s_axis_tdata[14] -attr @rip(#000000) s_axis_tdata[14] -port s_axis_tdata[14] -pin s_axis_tdata_IBUF[14]_inst I
load net s_axis_tdata[15] -attr @rip(#000000) s_axis_tdata[15] -port s_axis_tdata[15] -pin s_axis_tdata_IBUF[15]_inst I
load net s_axis_tdata[1] -attr @rip(#000000) s_axis_tdata[1] -port s_axis_tdata[1] -pin s_axis_tdata_IBUF[1]_inst I
load net s_axis_tdata[2] -attr @rip(#000000) s_axis_tdata[2] -port s_axis_tdata[2] -pin s_axis_tdata_IBUF[2]_inst I
load net s_axis_tdata[3] -attr @rip(#000000) s_axis_tdata[3] -port s_axis_tdata[3] -pin s_axis_tdata_IBUF[3]_inst I
load net s_axis_tdata[4] -attr @rip(#000000) s_axis_tdata[4] -port s_axis_tdata[4] -pin s_axis_tdata_IBUF[4]_inst I
load net s_axis_tdata[5] -attr @rip(#000000) s_axis_tdata[5] -port s_axis_tdata[5] -pin s_axis_tdata_IBUF[5]_inst I
load net s_axis_tdata[6] -attr @rip(#000000) s_axis_tdata[6] -port s_axis_tdata[6] -pin s_axis_tdata_IBUF[6]_inst I
load net s_axis_tdata[7] -attr @rip(#000000) s_axis_tdata[7] -port s_axis_tdata[7] -pin s_axis_tdata_IBUF[7]_inst I
load net s_axis_tdata[8] -attr @rip(#000000) s_axis_tdata[8] -port s_axis_tdata[8] -pin s_axis_tdata_IBUF[8]_inst I
load net s_axis_tdata[9] -attr @rip(#000000) s_axis_tdata[9] -port s_axis_tdata[9] -pin s_axis_tdata_IBUF[9]_inst I
load net s_axis_tdata_IBUF[0] -attr @rip(#000000) 0 -pin s_axis_tdata_IBUF[0]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[0]
load net s_axis_tdata_IBUF[10] -attr @rip(#000000) 10 -pin s_axis_tdata_IBUF[10]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[10]
load net s_axis_tdata_IBUF[11] -attr @rip(#000000) 11 -pin s_axis_tdata_IBUF[11]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[11]
load net s_axis_tdata_IBUF[12] -attr @rip(#000000) 12 -pin s_axis_tdata_IBUF[12]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[12]
load net s_axis_tdata_IBUF[13] -attr @rip(#000000) 13 -pin s_axis_tdata_IBUF[13]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[13]
load net s_axis_tdata_IBUF[14] -attr @rip(#000000) 14 -pin s_axis_tdata_IBUF[14]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[14]
load net s_axis_tdata_IBUF[15] -attr @rip(#000000) 15 -pin s_axis_tdata_IBUF[15]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[15]
load net s_axis_tdata_IBUF[1] -attr @rip(#000000) 1 -pin s_axis_tdata_IBUF[1]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[1]
load net s_axis_tdata_IBUF[2] -attr @rip(#000000) 2 -pin s_axis_tdata_IBUF[2]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[2]
load net s_axis_tdata_IBUF[3] -attr @rip(#000000) 3 -pin s_axis_tdata_IBUF[3]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[3]
load net s_axis_tdata_IBUF[4] -attr @rip(#000000) 4 -pin s_axis_tdata_IBUF[4]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[4]
load net s_axis_tdata_IBUF[5] -attr @rip(#000000) 5 -pin s_axis_tdata_IBUF[5]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[5]
load net s_axis_tdata_IBUF[6] -attr @rip(#000000) 6 -pin s_axis_tdata_IBUF[6]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[6]
load net s_axis_tdata_IBUF[7] -attr @rip(#000000) 7 -pin s_axis_tdata_IBUF[7]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[7]
load net s_axis_tdata_IBUF[8] -attr @rip(#000000) 8 -pin s_axis_tdata_IBUF[8]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[8]
load net s_axis_tdata_IBUF[9] -attr @rip(#000000) 9 -pin s_axis_tdata_IBUF[9]_inst O -pin u_input_buffer inbuf_reg[255][15]_0[9]
load net s_axis_tlast -port s_axis_tlast -pin s_axis_tlast_IBUF_inst I
netloc s_axis_tlast 1 0 3 NJ 1640 NJ 1640 NJ
load net s_axis_tlast_IBUF -pin s_axis_tlast_IBUF_inst O -pin u_input_buffer s_axis_tlast_IBUF
netloc s_axis_tlast_IBUF 1 3 1 NJ 1640
load net s_axis_tready -port s_axis_tready -pin s_axis_tready_OBUF_inst O
netloc s_axis_tready 1 6 1 NJ 1660
load net s_axis_tready_OBUF -pin s_axis_tready_OBUF_inst I -pin u_mac_engine s_axis_tready_OBUF
netloc s_axis_tready_OBUF 1 5 1 4990J 800n
load net s_axis_tvalid -port s_axis_tvalid -pin s_axis_tvalid_IBUF_inst I
netloc s_axis_tvalid 1 0 3 NJ 1730 NJ 1730 NJ
load net s_axis_tvalid_IBUF -pin s_axis_tvalid_IBUF_inst O -pin u_input_buffer s_axis_tvalid_IBUF -pin u_mac_engine s_axis_tvalid_IBUF
netloc s_axis_tvalid_IBUF 1 3 2 880 780 2990J
load net u_input_buffer_n_1 -attr @rip(#000000) D[15] -pin u_input_buffer D[15] -pin u_mac_engine D[15]
load net u_input_buffer_n_10 -attr @rip(#000000) D[6] -pin u_input_buffer D[6] -pin u_mac_engine D[6]
load net u_input_buffer_n_11 -attr @rip(#000000) D[5] -pin u_input_buffer D[5] -pin u_mac_engine D[5]
load net u_input_buffer_n_12 -attr @rip(#000000) D[4] -pin u_input_buffer D[4] -pin u_mac_engine D[4]
load net u_input_buffer_n_13 -attr @rip(#000000) D[3] -pin u_input_buffer D[3] -pin u_mac_engine D[3]
load net u_input_buffer_n_14 -attr @rip(#000000) D[2] -pin u_input_buffer D[2] -pin u_mac_engine D[2]
load net u_input_buffer_n_15 -attr @rip(#000000) D[1] -pin u_input_buffer D[1] -pin u_mac_engine D[1]
load net u_input_buffer_n_16 -attr @rip(#000000) D[0] -pin u_input_buffer D[0] -pin u_mac_engine D[0]
load net u_input_buffer_n_2 -attr @rip(#000000) D[14] -pin u_input_buffer D[14] -pin u_mac_engine D[14]
load net u_input_buffer_n_3 -attr @rip(#000000) D[13] -pin u_input_buffer D[13] -pin u_mac_engine D[13]
load net u_input_buffer_n_4 -attr @rip(#000000) D[12] -pin u_input_buffer D[12] -pin u_mac_engine D[12]
load net u_input_buffer_n_5 -attr @rip(#000000) D[11] -pin u_input_buffer D[11] -pin u_mac_engine D[11]
load net u_input_buffer_n_6 -attr @rip(#000000) D[10] -pin u_input_buffer D[10] -pin u_mac_engine D[10]
load net u_input_buffer_n_7 -attr @rip(#000000) D[9] -pin u_input_buffer D[9] -pin u_mac_engine D[9]
load net u_input_buffer_n_8 -attr @rip(#000000) D[8] -pin u_input_buffer D[8] -pin u_mac_engine D[8]
load net u_input_buffer_n_9 -attr @rip(#000000) D[7] -pin u_input_buffer D[7] -pin u_mac_engine D[7]
load net u_mac_engine_n_100 -pin u_mac_engine out_valid_reg_0 -pin u_relu_activation out_valid_reg_reg_0
netloc u_mac_engine_n_100 1 3 3 1420 520 2050J 1580 3910
load net u_mac_engine_n_101 -pin u_mac_engine wmem_raddr_reg[14]_5 -pin u_wmem_hidden mem_reg_bram_9_1
netloc u_mac_engine_n_101 1 3 3 1420 2480 NJ 2480 3810
load net u_mac_engine_n_102 -pin u_mac_engine wmem_raddr_reg[13]_8 -pin u_wmem_hidden mem_reg_bram_10_1
netloc u_mac_engine_n_102 1 3 3 1220 3280 NJ 3280 4790
load net u_mac_engine_n_103 -pin u_mac_engine wmem_raddr_reg[14]_6 -pin u_wmem_hidden mem_reg_bram_12_0
netloc u_mac_engine_n_103 1 3 3 1300 3320 NJ 3320 4630
load net u_mac_engine_n_104 -pin u_mac_engine wmem_raddr_reg[14]_7 -pin u_wmem_hidden mem_reg_bram_13_1
netloc u_mac_engine_n_104 1 3 3 1360 3360 NJ 3360 4550
load net u_mac_engine_n_105 -pin u_input_buffer a_val[0]_i_7_0 -pin u_mac_engine cur_input_reg[3]_rep_0
netloc u_mac_engine_n_105 1 3 3 1340 860 1950J 1680 4210
load net u_mac_engine_n_106 -pin u_input_buffer a_val_reg[8]_i_20_0 -pin u_mac_engine cur_input_reg[2]_rep_0
netloc u_mac_engine_n_106 1 3 3 1300 1820 NJ 1820 3790
load net u_mac_engine_n_107 -pin u_input_buffer a_val_reg[5]_i_18_0 -pin u_mac_engine cur_input_reg[2]_rep__1_0
netloc u_mac_engine_n_107 1 3 3 1280 1760 NJ 1760 4330
load net u_mac_engine_n_108 -pin u_input_buffer a_val_reg[14]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep_0
netloc u_mac_engine_n_108 1 3 3 1180 2120 NJ 2120 3870
load net u_mac_engine_n_109 -pin u_input_buffer a_val_reg[13]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep__0_0
netloc u_mac_engine_n_109 1 3 3 1140 2080 NJ 2080 4810
load net u_mac_engine_n_110 -pin u_input_buffer a_val_reg[12]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep__1_0
netloc u_mac_engine_n_110 1 3 3 1100 2040 NJ 2040 4770
load net u_mac_engine_n_111 -pin u_input_buffer a_val_reg[11]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep__2_0
netloc u_mac_engine_n_111 1 3 3 1060 2000 NJ 2000 4710
load net u_mac_engine_n_112 -pin u_input_buffer a_val_reg[10]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep__3_0
netloc u_mac_engine_n_112 1 3 3 1020 1960 NJ 1960 4650
load net u_mac_engine_n_113 -pin u_input_buffer a_val_reg[9]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep__4_0
netloc u_mac_engine_n_113 1 3 3 960 1920 NJ 1920 4590
load net u_mac_engine_n_114 -pin u_input_buffer a_val_reg[8]_i_49_0 -pin u_mac_engine cur_input_reg[1]_rep__5_0
netloc u_mac_engine_n_114 1 3 3 1360 1840 NJ 1840 4490
load net u_mac_engine_n_115 -pin u_input_buffer a_val_reg[3]_i_48_1 -pin u_mac_engine cur_input_reg[1]_rep__9_0
netloc u_mac_engine_n_115 1 3 3 1220 1860 NJ 1860 3930
load net u_mac_engine_n_116 -pin u_input_buffer a_val_reg[14]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep_0
netloc u_mac_engine_n_116 1 3 3 1380 2140 NJ 2140 4850
load net u_mac_engine_n_117 -pin u_input_buffer a_val_reg[13]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep__0_0
netloc u_mac_engine_n_117 1 3 3 1160 2100 NJ 2100 4510
load net u_mac_engine_n_118 -pin u_input_buffer a_val_reg[12]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep__1_0
netloc u_mac_engine_n_118 1 3 3 1120 2060 NJ 2060 4430
load net u_mac_engine_n_119 -pin u_input_buffer a_val_reg[11]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep__2_0
netloc u_mac_engine_n_119 1 3 3 1080 2020 NJ 2020 4350
load net u_mac_engine_n_120 -pin u_input_buffer a_val_reg[10]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep__3_0
netloc u_mac_engine_n_120 1 3 3 1040 1980 NJ 1980 4290
load net u_mac_engine_n_121 -pin u_input_buffer a_val_reg[9]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep__4_0
netloc u_mac_engine_n_121 1 3 3 980 1940 NJ 1940 4250
load net u_mac_engine_n_122 -pin u_input_buffer a_val_reg[8]_i_49_1 -pin u_mac_engine cur_input_reg[0]_rep__5_0
netloc u_mac_engine_n_122 1 3 3 1200 1880 NJ 1880 4190
load net u_mac_engine_n_123 -pin u_input_buffer a_val_reg[4]_i_29_0 -pin u_mac_engine cur_input_reg[0]_rep__8_0
netloc u_mac_engine_n_123 1 3 3 1000 1900 NJ 1900 4090
load net u_mac_engine_n_18 -pin u_input_buffer a_val_reg[1]_i_39_0 -pin u_mac_engine cur_input_reg[0]_rep__6_0
netloc u_mac_engine_n_18 1 3 3 1200 360 3150J 1380 3970
load net u_mac_engine_n_19 -attr @rip(#000000) Q[7] -pin u_input_buffer Q[7] -pin u_mac_engine Q[7]
load net u_mac_engine_n_20 -attr @rip(#000000) Q[6] -pin u_input_buffer Q[6] -pin u_mac_engine Q[6]
load net u_mac_engine_n_21 -attr @rip(#000000) Q[5] -pin u_input_buffer Q[5] -pin u_mac_engine Q[5]
load net u_mac_engine_n_22 -attr @rip(#000000) Q[4] -pin u_input_buffer Q[4] -pin u_mac_engine Q[4]
load net u_mac_engine_n_23 -attr @rip(#000000) Q[3] -pin u_input_buffer Q[3] -pin u_mac_engine Q[3]
load net u_mac_engine_n_24 -attr @rip(#000000) Q[2] -pin u_input_buffer Q[2] -pin u_mac_engine Q[2]
load net u_mac_engine_n_25 -attr @rip(#000000) Q[1] -pin u_input_buffer Q[1] -pin u_mac_engine Q[1]
load net u_mac_engine_n_26 -attr @rip(#000000) Q[0] -pin u_input_buffer Q[0] -pin u_mac_engine Q[0]
load net u_mac_engine_n_27 -pin u_input_buffer a_val_reg[6]_i_41_0 -pin u_mac_engine cur_input_reg[1]_rep__7_0
netloc u_mac_engine_n_27 1 3 3 1400 1740 NJ 1740 4410
load net u_mac_engine_n_28 -pin u_input_buffer a_val_reg[7]_i_25_0 -pin u_mac_engine cur_input_reg[0]_rep__10_0
netloc u_mac_engine_n_28 1 3 3 1260 1800 NJ 1800 3850
load net u_mac_engine_n_29 -pin u_input_buffer a_val_reg[7]_i_8_0 -pin u_mac_engine cur_input_reg[2]_rep__2_0
netloc u_mac_engine_n_29 1 3 3 1240 1780 NJ 1780 4270
load net u_mac_engine_n_30 -pin u_input_buffer a_val_reg[2]_i_13_0 -pin u_mac_engine cur_input_reg[2]_rep__0_0
netloc u_mac_engine_n_30 1 3 3 1220 380 3130J 1400 3750
load net u_mac_engine_n_31 -pin u_input_buffer a_val_reg[0]_i_55_0 -pin u_mac_engine cur_input_reg[1]_rep__11_0
netloc u_mac_engine_n_31 1 3 3 1280 400 3110J 1420 3890
load net u_mac_engine_n_32 -pin u_input_buffer a_val_reg[3]_i_48_0 -pin u_mac_engine cur_input_reg[0]_rep__7_0
netloc u_mac_engine_n_32 1 3 3 1180 420 3090J 1440 3830
load net u_mac_engine_n_33 -pin u_input_buffer a_val_reg[1]_i_36_0 -pin u_mac_engine cur_input_reg[1]_rep__10_0
netloc u_mac_engine_n_33 1 3 3 1240 440 3070J 1460 4010
load net u_mac_engine_n_34 -pin u_input_buffer a_val_reg[6]_i_38_0 -pin u_mac_engine cur_input_reg[0]_rep__9_0
netloc u_mac_engine_n_34 1 3 3 1340 1720 NJ 1720 3990
load net u_mac_engine_n_35 -pin u_input_buffer a_val_reg[4]_i_28_0 -pin u_mac_engine cur_input_reg[1]_rep__8_0
netloc u_mac_engine_n_35 1 3 3 1260 460 3050J 1480 4110
load net u_mac_engine_n_36 -pin u_mac_engine wmem_raddr_reg[13]_0 -pin u_wmem_hidden mem_reg_bram_1_0
netloc u_mac_engine_n_36 1 3 3 1040 2200 NJ 2200 4450
load net u_mac_engine_n_37 -pin u_mac_engine wmem_raddr_reg[12]_0 -pin u_wmem_hidden mem_reg_bram_2_0
netloc u_mac_engine_n_37 1 3 3 1080 2240 NJ 2240 4950
load net u_mac_engine_n_38 -pin u_mac_engine wmem_raddr_reg[12]_1 -pin u_wmem_hidden mem_reg_bram_3_0
netloc u_mac_engine_n_38 1 3 3 1120 2280 NJ 2280 4930
load net u_mac_engine_n_39 -pin u_mac_engine wmem_raddr_reg[12]_2 -pin u_wmem_hidden mem_reg_bram_4_0
netloc u_mac_engine_n_39 1 3 3 1380 3200 NJ 3200 4910
load net u_mac_engine_n_40 -pin u_mac_engine wmem_raddr_reg[12]_3 -pin u_wmem_hidden mem_reg_bram_5_0
netloc u_mac_engine_n_40 1 3 3 1340 3220 NJ 3220 4890
load net u_mac_engine_n_41 -pin u_mac_engine wmem_raddr_reg[13]_1 -pin u_wmem_hidden mem_reg_bram_6_0
netloc u_mac_engine_n_41 1 3 3 1260 3240 NJ 3240 4870
load net u_mac_engine_n_42 -pin u_mac_engine wmem_raddr_reg[13]_2 -pin u_wmem_hidden mem_reg_bram_7_0
netloc u_mac_engine_n_42 1 3 3 1240 3260 NJ 3260 4830
load net u_mac_engine_n_43 -pin u_mac_engine wmem_raddr_reg[14]_0 -pin u_wmem_hidden mem_reg_bram_13_0
netloc u_mac_engine_n_43 1 3 3 1320 3340 NJ 3340 4750
load net u_mac_engine_n_44 -pin u_mac_engine wmem_raddr_reg[14]_1 -pin u_wmem_hidden mem_reg_bram_11_0
netloc u_mac_engine_n_44 1 3 3 1400 3300 NJ 3300 4690
load net u_mac_engine_n_45 -pin u_mac_engine wmem_raddr_reg[14]_2 -pin u_wmem_hidden mem_reg_bram_9_0
netloc u_mac_engine_n_45 1 3 3 1200 2360 NJ 2360 4170
load net u_mac_engine_n_46 -pin u_mac_engine wmem_raddr_reg[13]_3 -pin u_wmem_hidden mem_reg_bram_10_0
netloc u_mac_engine_n_46 1 3 3 1220 2380 NJ 2380 4570
load net u_mac_engine_n_49 -attr @rip(#000000) SR[0] -pin u_mac_engine SR[0] -pin u_relu_activation SR[0]
netloc u_mac_engine_n_49 1 3 3 1400 800 2030J 1600 4670
load net u_mac_engine_n_90 -pin u_mac_engine wmem_raddr_reg[13]_4 -pin u_wmem_hidden mem_reg_bram_0_0
netloc u_mac_engine_n_90 1 3 3 1020 2180 NJ 2180 4370
load net u_mac_engine_n_91 -pin u_mac_engine wmem_raddr_reg[13]_5 -pin u_wmem_hidden mem_reg_bram_1_1
netloc u_mac_engine_n_91 1 3 3 1060 2220 NJ 2220 4310
load net u_mac_engine_n_92 -pin u_mac_engine wmem_raddr_reg[12]_4 -pin u_wmem_hidden mem_reg_bram_2_1
netloc u_mac_engine_n_92 1 3 3 1100 2260 NJ 2260 4530
load net u_mac_engine_n_93 -pin u_mac_engine wmem_raddr_reg[12]_5 -pin u_wmem_hidden mem_reg_bram_3_1
netloc u_mac_engine_n_93 1 3 3 1140 2300 NJ 2300 4230
load net u_mac_engine_n_94 -pin u_mac_engine wmem_raddr_reg[12]_6 -pin u_wmem_hidden mem_reg_bram_4_1
netloc u_mac_engine_n_94 1 3 3 1160 2320 NJ 2320 4150
load net u_mac_engine_n_95 -pin u_mac_engine wmem_raddr_reg[12]_7 -pin u_wmem_hidden mem_reg_bram_5_1
netloc u_mac_engine_n_95 1 3 3 1180 2340 NJ 2340 4050
load net u_mac_engine_n_96 -pin u_mac_engine wmem_raddr_reg[13]_6 -pin u_wmem_hidden mem_reg_bram_6_1
netloc u_mac_engine_n_96 1 3 3 1240 2400 NJ 2400 4470
load net u_mac_engine_n_97 -pin u_mac_engine wmem_raddr_reg[13]_7 -pin u_wmem_hidden mem_reg_bram_7_1
netloc u_mac_engine_n_97 1 3 3 1280 2420 NJ 2420 4390
load net u_mac_engine_n_98 -pin u_mac_engine wmem_raddr_reg[14]_3 -pin u_wmem_hidden mem_reg_bram_8_0
netloc u_mac_engine_n_98 1 3 3 1300 2440 NJ 2440 4070
load net u_mac_engine_n_99 -pin u_mac_engine wmem_raddr_reg[14]_4 -pin u_wmem_hidden mem_reg_bram_11_1
netloc u_mac_engine_n_99 1 3 3 1320 2460 NJ 2460 3950
load net u_relu_activation_n_4 -pin out_idx[1]_i_1 I1 -pin out_idx[2]_i_1 I1 -pin out_idx[6]_i_2 I1 -pin u_relu_activation out_idx_reg[4]
netloc u_relu_activation_n_4 1 1 4 180 3110 500J 3080 760J 3420 1890
load net vector_done -pin u_input_buffer vector_done -pin u_mac_engine vector_done
netloc vector_done 1 4 1 3030 780n
load net w_addr_h[0] -attr @rip(#000000) w_addr_h[0] -port w_addr_h[0] -pin w_addr_h_IBUF[0]_inst I
load net w_addr_h[1] -attr @rip(#000000) w_addr_h[1] -port w_addr_h[1] -pin w_addr_h_IBUF[1]_inst I
load net w_addr_h[2] -attr @rip(#000000) w_addr_h[2] -port w_addr_h[2] -pin w_addr_h_IBUF[2]_inst I
load net w_addr_h[3] -attr @rip(#000000) w_addr_h[3] -port w_addr_h[3] -pin w_addr_h_IBUF[3]_inst I
load net w_addr_h[4] -attr @rip(#000000) w_addr_h[4] -port w_addr_h[4] -pin w_addr_h_IBUF[4]_inst I
load net w_addr_h[5] -attr @rip(#000000) w_addr_h[5] -port w_addr_h[5] -pin w_addr_h_IBUF[5]_inst I
load net w_addr_h[6] -attr @rip(#000000) w_addr_h[6] -port w_addr_h[6] -pin w_addr_h_IBUF[6]_inst I
load net w_addr_h_IBUF[0] -attr @rip(#000000) 8 -pin u_wmem_hidden w_addr_reg_reg[14]_0[8] -pin w_addr_h_IBUF[0]_inst O
load net w_addr_h_IBUF[1] -attr @rip(#000000) 9 -pin u_wmem_hidden w_addr_reg_reg[14]_0[9] -pin w_addr_h_IBUF[1]_inst O
load net w_addr_h_IBUF[2] -attr @rip(#000000) 10 -pin u_wmem_hidden w_addr_reg_reg[14]_0[10] -pin w_addr_h_IBUF[2]_inst O
load net w_addr_h_IBUF[3] -attr @rip(#000000) 11 -pin u_wmem_hidden w_addr_reg_reg[14]_0[11] -pin w_addr_h_IBUF[3]_inst O
load net w_addr_h_IBUF[4] -attr @rip(#000000) 12 -pin u_wmem_hidden w_addr_reg_reg[14]_0[12] -pin w_addr_h_IBUF[4]_inst O
load net w_addr_h_IBUF[5] -attr @rip(#000000) 13 -pin u_wmem_hidden w_addr_reg_reg[14]_0[13] -pin w_addr_h_IBUF[5]_inst O
load net w_addr_h_IBUF[6] -attr @rip(#000000) 14 -pin u_wmem_hidden w_addr_reg_reg[14]_0[14] -pin w_addr_h_IBUF[6]_inst O
load net w_addr_i[0] -attr @rip(#000000) w_addr_i[0] -port w_addr_i[0] -pin w_addr_i_IBUF[0]_inst I
load net w_addr_i[1] -attr @rip(#000000) w_addr_i[1] -port w_addr_i[1] -pin w_addr_i_IBUF[1]_inst I
load net w_addr_i[2] -attr @rip(#000000) w_addr_i[2] -port w_addr_i[2] -pin w_addr_i_IBUF[2]_inst I
load net w_addr_i[3] -attr @rip(#000000) w_addr_i[3] -port w_addr_i[3] -pin w_addr_i_IBUF[3]_inst I
load net w_addr_i[4] -attr @rip(#000000) w_addr_i[4] -port w_addr_i[4] -pin w_addr_i_IBUF[4]_inst I
load net w_addr_i[5] -attr @rip(#000000) w_addr_i[5] -port w_addr_i[5] -pin w_addr_i_IBUF[5]_inst I
load net w_addr_i[6] -attr @rip(#000000) w_addr_i[6] -port w_addr_i[6] -pin w_addr_i_IBUF[6]_inst I
load net w_addr_i[7] -attr @rip(#000000) w_addr_i[7] -port w_addr_i[7] -pin w_addr_i_IBUF[7]_inst I
load net w_addr_i_IBUF[0] -attr @rip(#000000) 0 -pin u_wmem_hidden w_addr_reg_reg[14]_0[0] -pin w_addr_i_IBUF[0]_inst O
load net w_addr_i_IBUF[1] -attr @rip(#000000) 1 -pin u_wmem_hidden w_addr_reg_reg[14]_0[1] -pin w_addr_i_IBUF[1]_inst O
load net w_addr_i_IBUF[2] -attr @rip(#000000) 2 -pin u_wmem_hidden w_addr_reg_reg[14]_0[2] -pin w_addr_i_IBUF[2]_inst O
load net w_addr_i_IBUF[3] -attr @rip(#000000) 3 -pin u_wmem_hidden w_addr_reg_reg[14]_0[3] -pin w_addr_i_IBUF[3]_inst O
load net w_addr_i_IBUF[4] -attr @rip(#000000) 4 -pin u_wmem_hidden w_addr_reg_reg[14]_0[4] -pin w_addr_i_IBUF[4]_inst O
load net w_addr_i_IBUF[5] -attr @rip(#000000) 5 -pin u_wmem_hidden w_addr_reg_reg[14]_0[5] -pin w_addr_i_IBUF[5]_inst O
load net w_addr_i_IBUF[6] -attr @rip(#000000) 6 -pin u_wmem_hidden w_addr_reg_reg[14]_0[6] -pin w_addr_i_IBUF[6]_inst O
load net w_addr_i_IBUF[7] -attr @rip(#000000) 7 -pin u_wmem_hidden w_addr_reg_reg[14]_0[7] -pin w_addr_i_IBUF[7]_inst O
load net w_data[0] -attr @rip(#000000) w_data[0] -port w_data[0] -pin w_data_IBUF[0]_inst I
load net w_data[10] -attr @rip(#000000) w_data[10] -port w_data[10] -pin w_data_IBUF[10]_inst I
load net w_data[11] -attr @rip(#000000) w_data[11] -port w_data[11] -pin w_data_IBUF[11]_inst I
load net w_data[12] -attr @rip(#000000) w_data[12] -port w_data[12] -pin w_data_IBUF[12]_inst I
load net w_data[13] -attr @rip(#000000) w_data[13] -port w_data[13] -pin w_data_IBUF[13]_inst I
load net w_data[14] -attr @rip(#000000) w_data[14] -port w_data[14] -pin w_data_IBUF[14]_inst I
load net w_data[15] -attr @rip(#000000) w_data[15] -port w_data[15] -pin w_data_IBUF[15]_inst I
load net w_data[1] -attr @rip(#000000) w_data[1] -port w_data[1] -pin w_data_IBUF[1]_inst I
load net w_data[2] -attr @rip(#000000) w_data[2] -port w_data[2] -pin w_data_IBUF[2]_inst I
load net w_data[3] -attr @rip(#000000) w_data[3] -port w_data[3] -pin w_data_IBUF[3]_inst I
load net w_data[4] -attr @rip(#000000) w_data[4] -port w_data[4] -pin w_data_IBUF[4]_inst I
load net w_data[5] -attr @rip(#000000) w_data[5] -port w_data[5] -pin w_data_IBUF[5]_inst I
load net w_data[6] -attr @rip(#000000) w_data[6] -port w_data[6] -pin w_data_IBUF[6]_inst I
load net w_data[7] -attr @rip(#000000) w_data[7] -port w_data[7] -pin w_data_IBUF[7]_inst I
load net w_data[8] -attr @rip(#000000) w_data[8] -port w_data[8] -pin w_data_IBUF[8]_inst I
load net w_data[9] -attr @rip(#000000) w_data[9] -port w_data[9] -pin w_data_IBUF[9]_inst I
load net w_data_IBUF[0] -attr @rip(#000000) 0 -pin u_wmem_hidden D[0] -pin w_data_IBUF[0]_inst O
load net w_data_IBUF[10] -attr @rip(#000000) 10 -pin u_wmem_hidden D[10] -pin w_data_IBUF[10]_inst O
load net w_data_IBUF[11] -attr @rip(#000000) 11 -pin u_wmem_hidden D[11] -pin w_data_IBUF[11]_inst O
load net w_data_IBUF[12] -attr @rip(#000000) 12 -pin u_wmem_hidden D[12] -pin w_data_IBUF[12]_inst O
load net w_data_IBUF[13] -attr @rip(#000000) 13 -pin u_wmem_hidden D[13] -pin w_data_IBUF[13]_inst O
load net w_data_IBUF[14] -attr @rip(#000000) 14 -pin u_wmem_hidden D[14] -pin w_data_IBUF[14]_inst O
load net w_data_IBUF[15] -attr @rip(#000000) 15 -pin u_wmem_hidden D[15] -pin w_data_IBUF[15]_inst O
load net w_data_IBUF[1] -attr @rip(#000000) 1 -pin u_wmem_hidden D[1] -pin w_data_IBUF[1]_inst O
load net w_data_IBUF[2] -attr @rip(#000000) 2 -pin u_wmem_hidden D[2] -pin w_data_IBUF[2]_inst O
load net w_data_IBUF[3] -attr @rip(#000000) 3 -pin u_wmem_hidden D[3] -pin w_data_IBUF[3]_inst O
load net w_data_IBUF[4] -attr @rip(#000000) 4 -pin u_wmem_hidden D[4] -pin w_data_IBUF[4]_inst O
load net w_data_IBUF[5] -attr @rip(#000000) 5 -pin u_wmem_hidden D[5] -pin w_data_IBUF[5]_inst O
load net w_data_IBUF[6] -attr @rip(#000000) 6 -pin u_wmem_hidden D[6] -pin w_data_IBUF[6]_inst O
load net w_data_IBUF[7] -attr @rip(#000000) 7 -pin u_wmem_hidden D[7] -pin w_data_IBUF[7]_inst O
load net w_data_IBUF[8] -attr @rip(#000000) 8 -pin u_wmem_hidden D[8] -pin w_data_IBUF[8]_inst O
load net w_data_IBUF[9] -attr @rip(#000000) 9 -pin u_wmem_hidden D[9] -pin w_data_IBUF[9]_inst O
load net w_wr_en -port w_wr_en -pin w_wr_en_IBUF_inst I
netloc w_wr_en 1 0 3 NJ 3140 NJ 3140 NJ
load net w_wr_en_IBUF -pin u_wmem_hidden w_wr_en_IBUF -pin w_wr_en_IBUF_inst O
netloc w_wr_en_IBUF 1 3 1 NJ 3140
load net wmem_raddr[0] -attr @rip(#000000) wmem_raddr[0] -pin u_mac_engine wmem_raddr[0] -pin u_wmem_hidden wmem_raddr[0]
load net wmem_raddr[10] -attr @rip(#000000) wmem_raddr[10] -pin u_mac_engine wmem_raddr[10] -pin u_wmem_hidden wmem_raddr[10]
load net wmem_raddr[11] -attr @rip(#000000) wmem_raddr[11] -pin u_mac_engine wmem_raddr[11] -pin u_wmem_hidden wmem_raddr[11]
load net wmem_raddr[12] -attr @rip(#000000) wmem_raddr[12] -pin u_mac_engine wmem_raddr[12] -pin u_wmem_hidden wmem_raddr[12]
load net wmem_raddr[13] -attr @rip(#000000) wmem_raddr[13] -pin u_mac_engine wmem_raddr[13] -pin u_wmem_hidden wmem_raddr[13]
load net wmem_raddr[14] -attr @rip(#000000) wmem_raddr[14] -pin u_mac_engine wmem_raddr[14] -pin u_wmem_hidden wmem_raddr[14]
load net wmem_raddr[1] -attr @rip(#000000) wmem_raddr[1] -pin u_mac_engine wmem_raddr[1] -pin u_wmem_hidden wmem_raddr[1]
load net wmem_raddr[2] -attr @rip(#000000) wmem_raddr[2] -pin u_mac_engine wmem_raddr[2] -pin u_wmem_hidden wmem_raddr[2]
load net wmem_raddr[3] -attr @rip(#000000) wmem_raddr[3] -pin u_mac_engine wmem_raddr[3] -pin u_wmem_hidden wmem_raddr[3]
load net wmem_raddr[4] -attr @rip(#000000) wmem_raddr[4] -pin u_mac_engine wmem_raddr[4] -pin u_wmem_hidden wmem_raddr[4]
load net wmem_raddr[5] -attr @rip(#000000) wmem_raddr[5] -pin u_mac_engine wmem_raddr[5] -pin u_wmem_hidden wmem_raddr[5]
load net wmem_raddr[6] -attr @rip(#000000) wmem_raddr[6] -pin u_mac_engine wmem_raddr[6] -pin u_wmem_hidden wmem_raddr[6]
load net wmem_raddr[7] -attr @rip(#000000) wmem_raddr[7] -pin u_mac_engine wmem_raddr[7] -pin u_wmem_hidden wmem_raddr[7]
load net wmem_raddr[8] -attr @rip(#000000) wmem_raddr[8] -pin u_mac_engine wmem_raddr[8] -pin u_wmem_hidden wmem_raddr[8]
load net wmem_raddr[9] -attr @rip(#000000) wmem_raddr[9] -pin u_mac_engine wmem_raddr[9] -pin u_wmem_hidden wmem_raddr[9]
load net wmem_rdata[15] -attr @rip(#000000) DOUTBDOUT[0] -pin u_mac_engine DOUTBDOUT[0] -pin u_wmem_hidden DOUTBDOUT[0]
netloc wmem_rdata[15] 1 4 1 2970 620n
load net wr_ptr01_out -pin u_input_buffer wr_ptr01_out -pin u_mac_engine wr_ptr01_out
netloc wr_ptr01_out 1 3 3 1320 2160 NJ 2160 3730
load net u_relu_activation|<const1> -power -attr @name <const1> -pin u_relu_activation|out_valid_reg_reg CE
load net u_relu_activation|CLK -attr @name CLK -hierPin u_relu_activation CLK -pin u_relu_activation|out_data_reg_reg[0] C -pin u_relu_activation|out_data_reg_reg[10] C -pin u_relu_activation|out_data_reg_reg[11] C -pin u_relu_activation|out_data_reg_reg[12] C -pin u_relu_activation|out_data_reg_reg[13] C -pin u_relu_activation|out_data_reg_reg[14] C -pin u_relu_activation|out_data_reg_reg[15] C -pin u_relu_activation|out_data_reg_reg[16] C -pin u_relu_activation|out_data_reg_reg[17] C -pin u_relu_activation|out_data_reg_reg[18] C -pin u_relu_activation|out_data_reg_reg[19] C -pin u_relu_activation|out_data_reg_reg[1] C -pin u_relu_activation|out_data_reg_reg[20] C -pin u_relu_activation|out_data_reg_reg[21] C -pin u_relu_activation|out_data_reg_reg[22] C -pin u_relu_activation|out_data_reg_reg[23] C -pin u_relu_activation|out_data_reg_reg[24] C -pin u_relu_activation|out_data_reg_reg[25] C -pin u_relu_activation|out_data_reg_reg[26] C -pin u_relu_activation|out_data_reg_reg[27] C -pin u_relu_activation|out_data_reg_reg[28] C -pin u_relu_activation|out_data_reg_reg[29] C -pin u_relu_activation|out_data_reg_reg[2] C -pin u_relu_activation|out_data_reg_reg[30] C -pin u_relu_activation|out_data_reg_reg[31] C -pin u_relu_activation|out_data_reg_reg[32] C -pin u_relu_activation|out_data_reg_reg[33] C -pin u_relu_activation|out_data_reg_reg[34] C -pin u_relu_activation|out_data_reg_reg[35] C -pin u_relu_activation|out_data_reg_reg[36] C -pin u_relu_activation|out_data_reg_reg[37] C -pin u_relu_activation|out_data_reg_reg[38] C -pin u_relu_activation|out_data_reg_reg[39] C -pin u_relu_activation|out_data_reg_reg[3] C -pin u_relu_activation|out_data_reg_reg[4] C -pin u_relu_activation|out_data_reg_reg[5] C -pin u_relu_activation|out_data_reg_reg[6] C -pin u_relu_activation|out_data_reg_reg[7] C -pin u_relu_activation|out_data_reg_reg[8] C -pin u_relu_activation|out_data_reg_reg[9] C -pin u_relu_activation|out_valid_reg_reg C
netloc u_relu_activation|CLK 1 0 2 1660 6378 2020
load net u_relu_activation|D[0] -attr @rip(#000000) D[0] -attr @name D[0] -hierPin u_relu_activation D[0] -pin u_relu_activation|out_data_reg_reg[0] D
load net u_relu_activation|D[10] -attr @rip(#000000) D[10] -attr @name D[10] -hierPin u_relu_activation D[10] -pin u_relu_activation|out_data_reg_reg[10] D
load net u_relu_activation|D[11] -attr @rip(#000000) D[11] -attr @name D[11] -hierPin u_relu_activation D[11] -pin u_relu_activation|out_data_reg_reg[11] D
load net u_relu_activation|D[12] -attr @rip(#000000) D[12] -attr @name D[12] -hierPin u_relu_activation D[12] -pin u_relu_activation|out_data_reg_reg[12] D
load net u_relu_activation|D[13] -attr @rip(#000000) D[13] -attr @name D[13] -hierPin u_relu_activation D[13] -pin u_relu_activation|out_data_reg_reg[13] D
load net u_relu_activation|D[14] -attr @rip(#000000) D[14] -attr @name D[14] -hierPin u_relu_activation D[14] -pin u_relu_activation|out_data_reg_reg[14] D
load net u_relu_activation|D[15] -attr @rip(#000000) D[15] -attr @name D[15] -hierPin u_relu_activation D[15] -pin u_relu_activation|out_data_reg_reg[15] D
load net u_relu_activation|D[16] -attr @rip(#000000) D[16] -attr @name D[16] -hierPin u_relu_activation D[16] -pin u_relu_activation|out_data_reg_reg[16] D
load net u_relu_activation|D[17] -attr @rip(#000000) D[17] -attr @name D[17] -hierPin u_relu_activation D[17] -pin u_relu_activation|out_data_reg_reg[17] D
load net u_relu_activation|D[18] -attr @rip(#000000) D[18] -attr @name D[18] -hierPin u_relu_activation D[18] -pin u_relu_activation|out_data_reg_reg[18] D
load net u_relu_activation|D[19] -attr @rip(#000000) D[19] -attr @name D[19] -hierPin u_relu_activation D[19] -pin u_relu_activation|out_data_reg_reg[19] D
load net u_relu_activation|D[1] -attr @rip(#000000) D[1] -attr @name D[1] -hierPin u_relu_activation D[1] -pin u_relu_activation|out_data_reg_reg[1] D
load net u_relu_activation|D[20] -attr @rip(#000000) D[20] -attr @name D[20] -hierPin u_relu_activation D[20] -pin u_relu_activation|out_data_reg_reg[20] D
load net u_relu_activation|D[21] -attr @rip(#000000) D[21] -attr @name D[21] -hierPin u_relu_activation D[21] -pin u_relu_activation|out_data_reg_reg[21] D
load net u_relu_activation|D[22] -attr @rip(#000000) D[22] -attr @name D[22] -hierPin u_relu_activation D[22] -pin u_relu_activation|out_data_reg_reg[22] D
load net u_relu_activation|D[23] -attr @rip(#000000) D[23] -attr @name D[23] -hierPin u_relu_activation D[23] -pin u_relu_activation|out_data_reg_reg[23] D
load net u_relu_activation|D[24] -attr @rip(#000000) D[24] -attr @name D[24] -hierPin u_relu_activation D[24] -pin u_relu_activation|out_data_reg_reg[24] D
load net u_relu_activation|D[25] -attr @rip(#000000) D[25] -attr @name D[25] -hierPin u_relu_activation D[25] -pin u_relu_activation|out_data_reg_reg[25] D
load net u_relu_activation|D[26] -attr @rip(#000000) D[26] -attr @name D[26] -hierPin u_relu_activation D[26] -pin u_relu_activation|out_data_reg_reg[26] D
load net u_relu_activation|D[27] -attr @rip(#000000) D[27] -attr @name D[27] -hierPin u_relu_activation D[27] -pin u_relu_activation|out_data_reg_reg[27] D
load net u_relu_activation|D[28] -attr @rip(#000000) D[28] -attr @name D[28] -hierPin u_relu_activation D[28] -pin u_relu_activation|out_data_reg_reg[28] D
load net u_relu_activation|D[29] -attr @rip(#000000) D[29] -attr @name D[29] -hierPin u_relu_activation D[29] -pin u_relu_activation|out_data_reg_reg[29] D
load net u_relu_activation|D[2] -attr @rip(#000000) D[2] -attr @name D[2] -hierPin u_relu_activation D[2] -pin u_relu_activation|out_data_reg_reg[2] D
load net u_relu_activation|D[30] -attr @rip(#000000) D[30] -attr @name D[30] -hierPin u_relu_activation D[30] -pin u_relu_activation|out_data_reg_reg[30] D
load net u_relu_activation|D[31] -attr @rip(#000000) D[31] -attr @name D[31] -hierPin u_relu_activation D[31] -pin u_relu_activation|out_data_reg_reg[31] D
load net u_relu_activation|D[32] -attr @rip(#000000) D[32] -attr @name D[32] -hierPin u_relu_activation D[32] -pin u_relu_activation|out_data_reg_reg[32] D
load net u_relu_activation|D[33] -attr @rip(#000000) D[33] -attr @name D[33] -hierPin u_relu_activation D[33] -pin u_relu_activation|out_data_reg_reg[33] D
load net u_relu_activation|D[34] -attr @rip(#000000) D[34] -attr @name D[34] -hierPin u_relu_activation D[34] -pin u_relu_activation|out_data_reg_reg[34] D
load net u_relu_activation|D[35] -attr @rip(#000000) D[35] -attr @name D[35] -hierPin u_relu_activation D[35] -pin u_relu_activation|out_data_reg_reg[35] D
load net u_relu_activation|D[36] -attr @rip(#000000) D[36] -attr @name D[36] -hierPin u_relu_activation D[36] -pin u_relu_activation|out_data_reg_reg[36] D
load net u_relu_activation|D[37] -attr @rip(#000000) D[37] -attr @name D[37] -hierPin u_relu_activation D[37] -pin u_relu_activation|out_data_reg_reg[37] D
load net u_relu_activation|D[38] -attr @rip(#000000) D[38] -attr @name D[38] -hierPin u_relu_activation D[38] -pin u_relu_activation|out_data_reg_reg[38] D
load net u_relu_activation|D[39] -attr @rip(#000000) D[39] -attr @name D[39] -hierPin u_relu_activation D[39] -pin u_relu_activation|out_data_reg_reg[39] D
load net u_relu_activation|D[3] -attr @rip(#000000) D[3] -attr @name D[3] -hierPin u_relu_activation D[3] -pin u_relu_activation|out_data_reg_reg[3] D
load net u_relu_activation|D[4] -attr @rip(#000000) D[4] -attr @name D[4] -hierPin u_relu_activation D[4] -pin u_relu_activation|out_data_reg_reg[4] D
load net u_relu_activation|D[5] -attr @rip(#000000) D[5] -attr @name D[5] -hierPin u_relu_activation D[5] -pin u_relu_activation|out_data_reg_reg[5] D
load net u_relu_activation|D[6] -attr @rip(#000000) D[6] -attr @name D[6] -hierPin u_relu_activation D[6] -pin u_relu_activation|out_data_reg_reg[6] D
load net u_relu_activation|D[7] -attr @rip(#000000) D[7] -attr @name D[7] -hierPin u_relu_activation D[7] -pin u_relu_activation|out_data_reg_reg[7] D
load net u_relu_activation|D[8] -attr @rip(#000000) D[8] -attr @name D[8] -hierPin u_relu_activation D[8] -pin u_relu_activation|out_data_reg_reg[8] D
load net u_relu_activation|D[9] -attr @rip(#000000) D[9] -attr @name D[9] -hierPin u_relu_activation D[9] -pin u_relu_activation|out_data_reg_reg[9] D
load net u_relu_activation|E[0] -attr @rip(#000000) 0 -attr @name E[0] -hierPin u_relu_activation E[0] -pin u_relu_activation|out_idx[6]_i_1 O
netloc u_relu_activation|E[0] 1 2 1 2280 6588n
load net u_relu_activation|Q[0] -attr @rip(#000000) Q[0] -attr @name Q[0] -hierPin u_relu_activation Q[0] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 I2
load net u_relu_activation|Q[1] -attr @rip(#000000) Q[1] -attr @name Q[1] -hierPin u_relu_activation Q[1] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 I3
load net u_relu_activation|Q[2] -attr @rip(#000000) Q[2] -attr @name Q[2] -hierPin u_relu_activation Q[2] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 I1
load net u_relu_activation|Q[3] -attr @rip(#000000) Q[3] -attr @name Q[3] -hierPin u_relu_activation Q[3] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 I4
load net u_relu_activation|Q[4] -attr @rip(#000000) Q[4] -attr @name Q[4] -hierPin u_relu_activation Q[4] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 I0
load net u_relu_activation|Q[5] -attr @rip(#000000) Q[5] -attr @name Q[5] -hierPin u_relu_activation Q[5] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 I5
load net u_relu_activation|Q[6] -attr @rip(#000000) Q[6] -attr @name Q[6] -hierPin u_relu_activation Q[6] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_1 I1
load net u_relu_activation|SR[0] -attr @rip(#000000) SR[0] -attr @name SR[0] -hierPin u_relu_activation SR[0] -pin u_relu_activation|out_data_reg_reg[0] R -pin u_relu_activation|out_data_reg_reg[10] R -pin u_relu_activation|out_data_reg_reg[11] R -pin u_relu_activation|out_data_reg_reg[12] R -pin u_relu_activation|out_data_reg_reg[13] R -pin u_relu_activation|out_data_reg_reg[14] R -pin u_relu_activation|out_data_reg_reg[15] R -pin u_relu_activation|out_data_reg_reg[16] R -pin u_relu_activation|out_data_reg_reg[17] R -pin u_relu_activation|out_data_reg_reg[18] R -pin u_relu_activation|out_data_reg_reg[19] R -pin u_relu_activation|out_data_reg_reg[1] R -pin u_relu_activation|out_data_reg_reg[20] R -pin u_relu_activation|out_data_reg_reg[21] R -pin u_relu_activation|out_data_reg_reg[22] R -pin u_relu_activation|out_data_reg_reg[23] R -pin u_relu_activation|out_data_reg_reg[24] R -pin u_relu_activation|out_data_reg_reg[25] R -pin u_relu_activation|out_data_reg_reg[26] R -pin u_relu_activation|out_data_reg_reg[27] R -pin u_relu_activation|out_data_reg_reg[28] R -pin u_relu_activation|out_data_reg_reg[29] R -pin u_relu_activation|out_data_reg_reg[2] R -pin u_relu_activation|out_data_reg_reg[30] R -pin u_relu_activation|out_data_reg_reg[31] R -pin u_relu_activation|out_data_reg_reg[32] R -pin u_relu_activation|out_data_reg_reg[33] R -pin u_relu_activation|out_data_reg_reg[34] R -pin u_relu_activation|out_data_reg_reg[35] R -pin u_relu_activation|out_data_reg_reg[36] R -pin u_relu_activation|out_data_reg_reg[37] R -pin u_relu_activation|out_data_reg_reg[38] R -pin u_relu_activation|out_data_reg_reg[39] R -pin u_relu_activation|out_data_reg_reg[3] R -pin u_relu_activation|out_data_reg_reg[4] R -pin u_relu_activation|out_data_reg_reg[5] R -pin u_relu_activation|out_data_reg_reg[6] R -pin u_relu_activation|out_data_reg_reg[7] R -pin u_relu_activation|out_data_reg_reg[8] R -pin u_relu_activation|out_data_reg_reg[9] R
netloc u_relu_activation|SR[0] 1 0 2 NJ 6598 1920
load net u_relu_activation|m_axis_tlast_OBUF -attr @name m_axis_tlast_OBUF -hierPin u_relu_activation m_axis_tlast_OBUF -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_1 O
netloc u_relu_activation|m_axis_tlast_OBUF 1 2 1 N 6608
load net u_relu_activation|m_axis_tready_IBUF -attr @name m_axis_tready_IBUF -hierPin u_relu_activation m_axis_tready_IBUF -pin u_relu_activation|out_data_reg[39]_i_2 I1 -pin u_relu_activation|out_idx[6]_i_1 I0 -pin u_relu_activation|out_index[7]_i_3 I0
netloc u_relu_activation|m_axis_tready_IBUF 1 0 2 1640 6738 1920
load net u_relu_activation|m_axis_tvalid_OBUF -attr @name m_axis_tvalid_OBUF -hierPin u_relu_activation m_axis_tvalid_OBUF -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_1 I0 -pin u_relu_activation|out_data_reg[39]_i_2 I0 -pin u_relu_activation|out_idx[6]_i_1 I1 -pin u_relu_activation|out_index[7]_i_3 I1 -pin u_relu_activation|out_valid_reg_reg Q
netloc u_relu_activation|m_axis_tvalid_OBUF 1 0 3 1680 6618 1960 6668 NJ
load net u_relu_activation|mac_out_ready -attr @name mac_out_ready -hierPin u_relu_activation mac_out_ready -pin u_relu_activation|out_index[7]_i_3 O
netloc u_relu_activation|mac_out_ready 1 2 1 2340 6688n
load net u_relu_activation|mac_out_valid -attr @name mac_out_valid -hierPin u_relu_activation mac_out_valid -pin u_relu_activation|out_data_reg[39]_i_2 I2
netloc u_relu_activation|mac_out_valid 1 0 1 N 6698
load net u_relu_activation|out_data_reg -attr @name out_data_reg -pin u_relu_activation|out_data_reg[39]_i_2 O -pin u_relu_activation|out_data_reg_reg[0] CE -pin u_relu_activation|out_data_reg_reg[10] CE -pin u_relu_activation|out_data_reg_reg[11] CE -pin u_relu_activation|out_data_reg_reg[12] CE -pin u_relu_activation|out_data_reg_reg[13] CE -pin u_relu_activation|out_data_reg_reg[14] CE -pin u_relu_activation|out_data_reg_reg[15] CE -pin u_relu_activation|out_data_reg_reg[16] CE -pin u_relu_activation|out_data_reg_reg[17] CE -pin u_relu_activation|out_data_reg_reg[18] CE -pin u_relu_activation|out_data_reg_reg[19] CE -pin u_relu_activation|out_data_reg_reg[1] CE -pin u_relu_activation|out_data_reg_reg[20] CE -pin u_relu_activation|out_data_reg_reg[21] CE -pin u_relu_activation|out_data_reg_reg[22] CE -pin u_relu_activation|out_data_reg_reg[23] CE -pin u_relu_activation|out_data_reg_reg[24] CE -pin u_relu_activation|out_data_reg_reg[25] CE -pin u_relu_activation|out_data_reg_reg[26] CE -pin u_relu_activation|out_data_reg_reg[27] CE -pin u_relu_activation|out_data_reg_reg[28] CE -pin u_relu_activation|out_data_reg_reg[29] CE -pin u_relu_activation|out_data_reg_reg[2] CE -pin u_relu_activation|out_data_reg_reg[30] CE -pin u_relu_activation|out_data_reg_reg[31] CE -pin u_relu_activation|out_data_reg_reg[32] CE -pin u_relu_activation|out_data_reg_reg[33] CE -pin u_relu_activation|out_data_reg_reg[34] CE -pin u_relu_activation|out_data_reg_reg[35] CE -pin u_relu_activation|out_data_reg_reg[36] CE -pin u_relu_activation|out_data_reg_reg[37] CE -pin u_relu_activation|out_data_reg_reg[38] CE -pin u_relu_activation|out_data_reg_reg[39] CE -pin u_relu_activation|out_data_reg_reg[3] CE -pin u_relu_activation|out_data_reg_reg[4] CE -pin u_relu_activation|out_data_reg_reg[5] CE -pin u_relu_activation|out_data_reg_reg[6] CE -pin u_relu_activation|out_data_reg_reg[7] CE -pin u_relu_activation|out_data_reg_reg[8] CE -pin u_relu_activation|out_data_reg_reg[9] CE
netloc u_relu_activation|out_data_reg 1 1 1 2000 618n
load net u_relu_activation|out_data_reg_reg[39]_0[0] -attr @rip(#000000) 0 -attr @name out_data_reg_reg[39]_0[0] -hierPin u_relu_activation out_data_reg_reg[39]_0[0] -pin u_relu_activation|out_data_reg_reg[0] Q
load net u_relu_activation|out_data_reg_reg[39]_0[10] -attr @rip(#000000) 10 -attr @name out_data_reg_reg[39]_0[10] -hierPin u_relu_activation out_data_reg_reg[39]_0[10] -pin u_relu_activation|out_data_reg_reg[10] Q
load net u_relu_activation|out_data_reg_reg[39]_0[11] -attr @rip(#000000) 11 -attr @name out_data_reg_reg[39]_0[11] -hierPin u_relu_activation out_data_reg_reg[39]_0[11] -pin u_relu_activation|out_data_reg_reg[11] Q
load net u_relu_activation|out_data_reg_reg[39]_0[12] -attr @rip(#000000) 12 -attr @name out_data_reg_reg[39]_0[12] -hierPin u_relu_activation out_data_reg_reg[39]_0[12] -pin u_relu_activation|out_data_reg_reg[12] Q
load net u_relu_activation|out_data_reg_reg[39]_0[13] -attr @rip(#000000) 13 -attr @name out_data_reg_reg[39]_0[13] -hierPin u_relu_activation out_data_reg_reg[39]_0[13] -pin u_relu_activation|out_data_reg_reg[13] Q
load net u_relu_activation|out_data_reg_reg[39]_0[14] -attr @rip(#000000) 14 -attr @name out_data_reg_reg[39]_0[14] -hierPin u_relu_activation out_data_reg_reg[39]_0[14] -pin u_relu_activation|out_data_reg_reg[14] Q
load net u_relu_activation|out_data_reg_reg[39]_0[15] -attr @rip(#000000) 15 -attr @name out_data_reg_reg[39]_0[15] -hierPin u_relu_activation out_data_reg_reg[39]_0[15] -pin u_relu_activation|out_data_reg_reg[15] Q
load net u_relu_activation|out_data_reg_reg[39]_0[16] -attr @rip(#000000) 16 -attr @name out_data_reg_reg[39]_0[16] -hierPin u_relu_activation out_data_reg_reg[39]_0[16] -pin u_relu_activation|out_data_reg_reg[16] Q
load net u_relu_activation|out_data_reg_reg[39]_0[17] -attr @rip(#000000) 17 -attr @name out_data_reg_reg[39]_0[17] -hierPin u_relu_activation out_data_reg_reg[39]_0[17] -pin u_relu_activation|out_data_reg_reg[17] Q
load net u_relu_activation|out_data_reg_reg[39]_0[18] -attr @rip(#000000) 18 -attr @name out_data_reg_reg[39]_0[18] -hierPin u_relu_activation out_data_reg_reg[39]_0[18] -pin u_relu_activation|out_data_reg_reg[18] Q
load net u_relu_activation|out_data_reg_reg[39]_0[19] -attr @rip(#000000) 19 -attr @name out_data_reg_reg[39]_0[19] -hierPin u_relu_activation out_data_reg_reg[39]_0[19] -pin u_relu_activation|out_data_reg_reg[19] Q
load net u_relu_activation|out_data_reg_reg[39]_0[1] -attr @rip(#000000) 1 -attr @name out_data_reg_reg[39]_0[1] -hierPin u_relu_activation out_data_reg_reg[39]_0[1] -pin u_relu_activation|out_data_reg_reg[1] Q
load net u_relu_activation|out_data_reg_reg[39]_0[20] -attr @rip(#000000) 20 -attr @name out_data_reg_reg[39]_0[20] -hierPin u_relu_activation out_data_reg_reg[39]_0[20] -pin u_relu_activation|out_data_reg_reg[20] Q
load net u_relu_activation|out_data_reg_reg[39]_0[21] -attr @rip(#000000) 21 -attr @name out_data_reg_reg[39]_0[21] -hierPin u_relu_activation out_data_reg_reg[39]_0[21] -pin u_relu_activation|out_data_reg_reg[21] Q
load net u_relu_activation|out_data_reg_reg[39]_0[22] -attr @rip(#000000) 22 -attr @name out_data_reg_reg[39]_0[22] -hierPin u_relu_activation out_data_reg_reg[39]_0[22] -pin u_relu_activation|out_data_reg_reg[22] Q
load net u_relu_activation|out_data_reg_reg[39]_0[23] -attr @rip(#000000) 23 -attr @name out_data_reg_reg[39]_0[23] -hierPin u_relu_activation out_data_reg_reg[39]_0[23] -pin u_relu_activation|out_data_reg_reg[23] Q
load net u_relu_activation|out_data_reg_reg[39]_0[24] -attr @rip(#000000) 24 -attr @name out_data_reg_reg[39]_0[24] -hierPin u_relu_activation out_data_reg_reg[39]_0[24] -pin u_relu_activation|out_data_reg_reg[24] Q
load net u_relu_activation|out_data_reg_reg[39]_0[25] -attr @rip(#000000) 25 -attr @name out_data_reg_reg[39]_0[25] -hierPin u_relu_activation out_data_reg_reg[39]_0[25] -pin u_relu_activation|out_data_reg_reg[25] Q
load net u_relu_activation|out_data_reg_reg[39]_0[26] -attr @rip(#000000) 26 -attr @name out_data_reg_reg[39]_0[26] -hierPin u_relu_activation out_data_reg_reg[39]_0[26] -pin u_relu_activation|out_data_reg_reg[26] Q
load net u_relu_activation|out_data_reg_reg[39]_0[27] -attr @rip(#000000) 27 -attr @name out_data_reg_reg[39]_0[27] -hierPin u_relu_activation out_data_reg_reg[39]_0[27] -pin u_relu_activation|out_data_reg_reg[27] Q
load net u_relu_activation|out_data_reg_reg[39]_0[28] -attr @rip(#000000) 28 -attr @name out_data_reg_reg[39]_0[28] -hierPin u_relu_activation out_data_reg_reg[39]_0[28] -pin u_relu_activation|out_data_reg_reg[28] Q
load net u_relu_activation|out_data_reg_reg[39]_0[29] -attr @rip(#000000) 29 -attr @name out_data_reg_reg[39]_0[29] -hierPin u_relu_activation out_data_reg_reg[39]_0[29] -pin u_relu_activation|out_data_reg_reg[29] Q
load net u_relu_activation|out_data_reg_reg[39]_0[2] -attr @rip(#000000) 2 -attr @name out_data_reg_reg[39]_0[2] -hierPin u_relu_activation out_data_reg_reg[39]_0[2] -pin u_relu_activation|out_data_reg_reg[2] Q
load net u_relu_activation|out_data_reg_reg[39]_0[30] -attr @rip(#000000) 30 -attr @name out_data_reg_reg[39]_0[30] -hierPin u_relu_activation out_data_reg_reg[39]_0[30] -pin u_relu_activation|out_data_reg_reg[30] Q
load net u_relu_activation|out_data_reg_reg[39]_0[31] -attr @rip(#000000) 31 -attr @name out_data_reg_reg[39]_0[31] -hierPin u_relu_activation out_data_reg_reg[39]_0[31] -pin u_relu_activation|out_data_reg_reg[31] Q
load net u_relu_activation|out_data_reg_reg[39]_0[32] -attr @rip(#000000) 32 -attr @name out_data_reg_reg[39]_0[32] -hierPin u_relu_activation out_data_reg_reg[39]_0[32] -pin u_relu_activation|out_data_reg_reg[32] Q
load net u_relu_activation|out_data_reg_reg[39]_0[33] -attr @rip(#000000) 33 -attr @name out_data_reg_reg[39]_0[33] -hierPin u_relu_activation out_data_reg_reg[39]_0[33] -pin u_relu_activation|out_data_reg_reg[33] Q
load net u_relu_activation|out_data_reg_reg[39]_0[34] -attr @rip(#000000) 34 -attr @name out_data_reg_reg[39]_0[34] -hierPin u_relu_activation out_data_reg_reg[39]_0[34] -pin u_relu_activation|out_data_reg_reg[34] Q
load net u_relu_activation|out_data_reg_reg[39]_0[35] -attr @rip(#000000) 35 -attr @name out_data_reg_reg[39]_0[35] -hierPin u_relu_activation out_data_reg_reg[39]_0[35] -pin u_relu_activation|out_data_reg_reg[35] Q
load net u_relu_activation|out_data_reg_reg[39]_0[36] -attr @rip(#000000) 36 -attr @name out_data_reg_reg[39]_0[36] -hierPin u_relu_activation out_data_reg_reg[39]_0[36] -pin u_relu_activation|out_data_reg_reg[36] Q
load net u_relu_activation|out_data_reg_reg[39]_0[37] -attr @rip(#000000) 37 -attr @name out_data_reg_reg[39]_0[37] -hierPin u_relu_activation out_data_reg_reg[39]_0[37] -pin u_relu_activation|out_data_reg_reg[37] Q
load net u_relu_activation|out_data_reg_reg[39]_0[38] -attr @rip(#000000) 38 -attr @name out_data_reg_reg[39]_0[38] -hierPin u_relu_activation out_data_reg_reg[39]_0[38] -pin u_relu_activation|out_data_reg_reg[38] Q
load net u_relu_activation|out_data_reg_reg[39]_0[39] -attr @rip(#000000) 39 -attr @name out_data_reg_reg[39]_0[39] -hierPin u_relu_activation out_data_reg_reg[39]_0[39] -pin u_relu_activation|out_data_reg_reg[39] Q
load net u_relu_activation|out_data_reg_reg[39]_0[3] -attr @rip(#000000) 3 -attr @name out_data_reg_reg[39]_0[3] -hierPin u_relu_activation out_data_reg_reg[39]_0[3] -pin u_relu_activation|out_data_reg_reg[3] Q
load net u_relu_activation|out_data_reg_reg[39]_0[4] -attr @rip(#000000) 4 -attr @name out_data_reg_reg[39]_0[4] -hierPin u_relu_activation out_data_reg_reg[39]_0[4] -pin u_relu_activation|out_data_reg_reg[4] Q
load net u_relu_activation|out_data_reg_reg[39]_0[5] -attr @rip(#000000) 5 -attr @name out_data_reg_reg[39]_0[5] -hierPin u_relu_activation out_data_reg_reg[39]_0[5] -pin u_relu_activation|out_data_reg_reg[5] Q
load net u_relu_activation|out_data_reg_reg[39]_0[6] -attr @rip(#000000) 6 -attr @name out_data_reg_reg[39]_0[6] -hierPin u_relu_activation out_data_reg_reg[39]_0[6] -pin u_relu_activation|out_data_reg_reg[6] Q
load net u_relu_activation|out_data_reg_reg[39]_0[7] -attr @rip(#000000) 7 -attr @name out_data_reg_reg[39]_0[7] -hierPin u_relu_activation out_data_reg_reg[39]_0[7] -pin u_relu_activation|out_data_reg_reg[7] Q
load net u_relu_activation|out_data_reg_reg[39]_0[8] -attr @rip(#000000) 8 -attr @name out_data_reg_reg[39]_0[8] -hierPin u_relu_activation out_data_reg_reg[39]_0[8] -pin u_relu_activation|out_data_reg_reg[8] Q
load net u_relu_activation|out_data_reg_reg[39]_0[9] -attr @rip(#000000) 9 -attr @name out_data_reg_reg[39]_0[9] -hierPin u_relu_activation out_data_reg_reg[39]_0[9] -pin u_relu_activation|out_data_reg_reg[9] Q
load net u_relu_activation|out_idx_reg[4] -attr @name out_idx_reg[4] -hierPin u_relu_activation out_idx_reg[4] -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_1 I2 -pin u_relu_activation|m_axis_tlast_OBUF_inst_i_2 O
netloc u_relu_activation|out_idx_reg[4] 1 1 2 1980 6688 2300J
load net u_relu_activation|out_valid_reg_reg_0 -attr @name out_valid_reg_reg_0 -hierPin u_relu_activation out_valid_reg_reg_0 -pin u_relu_activation|out_valid_reg_reg D
netloc u_relu_activation|out_valid_reg_reg_0 1 0 1 N 6848
load net u_relu_activation|p_0_in -attr @name p_0_in -hierPin u_relu_activation p_0_in -pin u_relu_activation|out_valid_reg_reg R
netloc u_relu_activation|p_0_in 1 0 1 N 6868
load netBundle @u_relu_activation|D 40 u_relu_activation|D[39] u_relu_activation|D[38] u_relu_activation|D[37] u_relu_activation|D[36] u_relu_activation|D[35] u_relu_activation|D[34] u_relu_activation|D[33] u_relu_activation|D[32] u_relu_activation|D[31] u_relu_activation|D[30] u_relu_activation|D[29] u_relu_activation|D[28] u_relu_activation|D[27] u_relu_activation|D[26] u_relu_activation|D[25] u_relu_activation|D[24] u_relu_activation|D[23] u_relu_activation|D[22] u_relu_activation|D[21] u_relu_activation|D[20] u_relu_activation|D[19] u_relu_activation|D[18] u_relu_activation|D[17] u_relu_activation|D[16] u_relu_activation|D[15] u_relu_activation|D[14] u_relu_activation|D[13] u_relu_activation|D[12] u_relu_activation|D[11] u_relu_activation|D[10] u_relu_activation|D[9] u_relu_activation|D[8] u_relu_activation|D[7] u_relu_activation|D[6] u_relu_activation|D[5] u_relu_activation|D[4] u_relu_activation|D[3] u_relu_activation|D[2] u_relu_activation|D[1] u_relu_activation|D[0] -autobundled
netbloc @u_relu_activation|D 1 0 2 NJ 6398 2040
load netBundle @u_relu_activation|Q 7 u_relu_activation|Q[6] u_relu_activation|Q[5] u_relu_activation|Q[4] u_relu_activation|Q[3] u_relu_activation|Q[2] u_relu_activation|Q[1] u_relu_activation|Q[0] -autobundled
netbloc @u_relu_activation|Q 1 0 2 1680 6578 1940
load netBundle @u_relu_activation|out_data_reg 40 u_relu_activation|out_data_reg_reg[39]_0[39] u_relu_activation|out_data_reg_reg[39]_0[38] u_relu_activation|out_data_reg_reg[39]_0[37] u_relu_activation|out_data_reg_reg[39]_0[36] u_relu_activation|out_data_reg_reg[39]_0[35] u_relu_activation|out_data_reg_reg[39]_0[34] u_relu_activation|out_data_reg_reg[39]_0[33] u_relu_activation|out_data_reg_reg[39]_0[32] u_relu_activation|out_data_reg_reg[39]_0[31] u_relu_activation|out_data_reg_reg[39]_0[30] u_relu_activation|out_data_reg_reg[39]_0[29] u_relu_activation|out_data_reg_reg[39]_0[28] u_relu_activation|out_data_reg_reg[39]_0[27] u_relu_activation|out_data_reg_reg[39]_0[26] u_relu_activation|out_data_reg_reg[39]_0[25] u_relu_activation|out_data_reg_reg[39]_0[24] u_relu_activation|out_data_reg_reg[39]_0[23] u_relu_activation|out_data_reg_reg[39]_0[22] u_relu_activation|out_data_reg_reg[39]_0[21] u_relu_activation|out_data_reg_reg[39]_0[20] u_relu_activation|out_data_reg_reg[39]_0[19] u_relu_activation|out_data_reg_reg[39]_0[18] u_relu_activation|out_data_reg_reg[39]_0[17] u_relu_activation|out_data_reg_reg[39]_0[16] u_relu_activation|out_data_reg_reg[39]_0[15] u_relu_activation|out_data_reg_reg[39]_0[14] u_relu_activation|out_data_reg_reg[39]_0[13] u_relu_activation|out_data_reg_reg[39]_0[12] u_relu_activation|out_data_reg_reg[39]_0[11] u_relu_activation|out_data_reg_reg[39]_0[10] u_relu_activation|out_data_reg_reg[39]_0[9] u_relu_activation|out_data_reg_reg[39]_0[8] u_relu_activation|out_data_reg_reg[39]_0[7] u_relu_activation|out_data_reg_reg[39]_0[6] u_relu_activation|out_data_reg_reg[39]_0[5] u_relu_activation|out_data_reg_reg[39]_0[4] u_relu_activation|out_data_reg_reg[39]_0[3] u_relu_activation|out_data_reg_reg[39]_0[2] u_relu_activation|out_data_reg_reg[39]_0[1] u_relu_activation|out_data_reg_reg[39]_0[0] -autobundled
netbloc @u_relu_activation|out_data_reg 1 2 1 2320 628n
load netBundle @s_axis_tdata 16 s_axis_tdata[15] s_axis_tdata[14] s_axis_tdata[13] s_axis_tdata[12] s_axis_tdata[11] s_axis_tdata[10] s_axis_tdata[9] s_axis_tdata[8] s_axis_tdata[7] s_axis_tdata[6] s_axis_tdata[5] s_axis_tdata[4] s_axis_tdata[3] s_axis_tdata[2] s_axis_tdata[1] s_axis_tdata[0] -autobundled
netbloc @s_axis_tdata 1 0 3 NJ 60 NJ 60 500
load netBundle @w_addr_h 7 w_addr_h[6] w_addr_h[5] w_addr_h[4] w_addr_h[3] w_addr_h[2] w_addr_h[1] w_addr_h[0] -autobundled
netbloc @w_addr_h 1 0 3 NJ 3240 NJ 3240 460
load netBundle @w_addr_i 8 w_addr_i[7] w_addr_i[6] w_addr_i[5] w_addr_i[4] w_addr_i[3] w_addr_i[2] w_addr_i[1] w_addr_i[0] -autobundled
netbloc @w_addr_i 1 0 3 NJ 3870 NJ 3870 500
load netBundle @w_data 16 w_data[15] w_data[14] w_data[13] w_data[12] w_data[11] w_data[10] w_data[9] w_data[8] w_data[7] w_data[6] w_data[5] w_data[4] w_data[3] w_data[2] w_data[1] w_data[0] -autobundled
netbloc @w_data 1 0 3 NJ 4590 NJ 4590 460
load netBundle @m_axis_tdata 40 m_axis_tdata[39] m_axis_tdata[38] m_axis_tdata[37] m_axis_tdata[36] m_axis_tdata[35] m_axis_tdata[34] m_axis_tdata[33] m_axis_tdata[32] m_axis_tdata[31] m_axis_tdata[30] m_axis_tdata[29] m_axis_tdata[28] m_axis_tdata[27] m_axis_tdata[26] m_axis_tdata[25] m_axis_tdata[24] m_axis_tdata[23] m_axis_tdata[22] m_axis_tdata[21] m_axis_tdata[20] m_axis_tdata[19] m_axis_tdata[18] m_axis_tdata[17] m_axis_tdata[16] m_axis_tdata[15] m_axis_tdata[14] m_axis_tdata[13] m_axis_tdata[12] m_axis_tdata[11] m_axis_tdata[10] m_axis_tdata[9] m_axis_tdata[8] m_axis_tdata[7] m_axis_tdata[6] m_axis_tdata[5] m_axis_tdata[4] m_axis_tdata[3] m_axis_tdata[2] m_axis_tdata[1] m_axis_tdata[0] -autobundled
netbloc @m_axis_tdata 1 6 1 5300 1170n
load netBundle @u_input_buffer_n_ 16 u_input_buffer_n_1 u_input_buffer_n_2 u_input_buffer_n_3 u_input_buffer_n_4 u_input_buffer_n_5 u_input_buffer_n_6 u_input_buffer_n_7 u_input_buffer_n_8 u_input_buffer_n_9 u_input_buffer_n_10 u_input_buffer_n_11 u_input_buffer_n_12 u_input_buffer_n_13 u_input_buffer_n_14 u_input_buffer_n_15 u_input_buffer_n_16 -autobundled
netbloc @u_input_buffer_n_ 1 4 1 2070 600n
load netBundle @u_mac_engine_n_ 8 u_mac_engine_n_19 u_mac_engine_n_20 u_mac_engine_n_21 u_mac_engine_n_22 u_mac_engine_n_23 u_mac_engine_n_24 u_mac_engine_n_25 u_mac_engine_n_26 -autobundled
netbloc @u_mac_engine_n_ 1 3 3 1300 840 1970J 1660 4730
load netBundle @mac_out_data 40 mac_out_data[39] mac_out_data[38] mac_out_data[37] mac_out_data[36] mac_out_data[35] mac_out_data[34] mac_out_data[33] mac_out_data[32] mac_out_data[31] mac_out_data[30] mac_out_data[29] mac_out_data[28] mac_out_data[27] mac_out_data[26] mac_out_data[25] mac_out_data[24] mac_out_data[23] mac_out_data[22] mac_out_data[21] mac_out_data[20] mac_out_data[19] mac_out_data[18] mac_out_data[17] mac_out_data[16] mac_out_data[15] mac_out_data[14] mac_out_data[13] mac_out_data[12] mac_out_data[11] mac_out_data[10] mac_out_data[9] mac_out_data[8] mac_out_data[7] mac_out_data[6] mac_out_data[5] mac_out_data[4] mac_out_data[3] mac_out_data[2] mac_out_data[1] mac_out_data[0] -autobundled
netbloc @mac_out_data 1 3 3 1300 480 2950J 1540 4030
load netBundle @wmem_raddr 15 wmem_raddr[14] wmem_raddr[13] wmem_raddr[12] wmem_raddr[11] wmem_raddr[10] wmem_raddr[9] wmem_raddr[8] wmem_raddr[7] wmem_raddr[6] wmem_raddr[5] wmem_raddr[4] wmem_raddr[3] wmem_raddr[2] wmem_raddr[1] wmem_raddr[0] -autobundled
netbloc @wmem_raddr 1 3 3 1280 3380 NJ 3380 4970
load netBundle @m_axis_tdata_OBUF 40 m_axis_tdata_OBUF[39] m_axis_tdata_OBUF[38] m_axis_tdata_OBUF[37] m_axis_tdata_OBUF[36] m_axis_tdata_OBUF[35] m_axis_tdata_OBUF[34] m_axis_tdata_OBUF[33] m_axis_tdata_OBUF[32] m_axis_tdata_OBUF[31] m_axis_tdata_OBUF[30] m_axis_tdata_OBUF[29] m_axis_tdata_OBUF[28] m_axis_tdata_OBUF[27] m_axis_tdata_OBUF[26] m_axis_tdata_OBUF[25] m_axis_tdata_OBUF[24] m_axis_tdata_OBUF[23] m_axis_tdata_OBUF[22] m_axis_tdata_OBUF[21] m_axis_tdata_OBUF[20] m_axis_tdata_OBUF[19] m_axis_tdata_OBUF[18] m_axis_tdata_OBUF[17] m_axis_tdata_OBUF[16] m_axis_tdata_OBUF[15] m_axis_tdata_OBUF[14] m_axis_tdata_OBUF[13] m_axis_tdata_OBUF[12] m_axis_tdata_OBUF[11] m_axis_tdata_OBUF[10] m_axis_tdata_OBUF[9] m_axis_tdata_OBUF[8] m_axis_tdata_OBUF[7] m_axis_tdata_OBUF[6] m_axis_tdata_OBUF[5] m_axis_tdata_OBUF[4] m_axis_tdata_OBUF[3] m_axis_tdata_OBUF[2] m_axis_tdata_OBUF[1] m_axis_tdata_OBUF[0] -autobundled
netbloc @m_axis_tdata_OBUF 1 4 2 2010 1640 5010
load netBundle @p_2_out 16 p_2_out[15] p_2_out[14] p_2_out[13] p_2_out[12] p_2_out[11] p_2_out[10] p_2_out[9] p_2_out[8] p_2_out[7] p_2_out[6] p_2_out[5] p_2_out[4] p_2_out[3] p_2_out[2] p_2_out[1] p_2_out[0] -autobundled
netbloc @p_2_out 1 4 1 3010 640n
load netBundle @s_axis_tdata_IBUF 16 s_axis_tdata_IBUF[15] s_axis_tdata_IBUF[14] s_axis_tdata_IBUF[13] s_axis_tdata_IBUF[12] s_axis_tdata_IBUF[11] s_axis_tdata_IBUF[10] s_axis_tdata_IBUF[9] s_axis_tdata_IBUF[8] s_axis_tdata_IBUF[7] s_axis_tdata_IBUF[6] s_axis_tdata_IBUF[5] s_axis_tdata_IBUF[4] s_axis_tdata_IBUF[3] s_axis_tdata_IBUF[2] s_axis_tdata_IBUF[1] s_axis_tdata_IBUF[0] -autobundled
netbloc @s_axis_tdata_IBUF 1 3 1 760 60n
load netBundle @out_idx 7 out_idx[6] out_idx[5] out_idx[4] out_idx[3] out_idx[2] out_idx[1] out_idx[0] -autobundled
netbloc @out_idx 1 1 3 160 3180 NJ 3180 800
load netBundle @w_data_IBUF 16 w_data_IBUF[15] w_data_IBUF[14] w_data_IBUF[13] w_data_IBUF[12] w_data_IBUF[11] w_data_IBUF[10] w_data_IBUF[9] w_data_IBUF[8] w_data_IBUF[7] w_data_IBUF[6] w_data_IBUF[5] w_data_IBUF[4] w_data_IBUF[3] w_data_IBUF[2] w_data_IBUF[1] w_data_IBUF[0] -autobundled
netbloc @w_data_IBUF 1 3 1 820 2560n
load netBundle @w_addr_i_IBUF,w_addr_h_IBUF 15 w_addr_h_IBUF[6] w_addr_h_IBUF[5] w_addr_h_IBUF[4] w_addr_h_IBUF[3] w_addr_h_IBUF[2] w_addr_h_IBUF[1] w_addr_h_IBUF[0] w_addr_i_IBUF[7] w_addr_i_IBUF[6] w_addr_i_IBUF[5] w_addr_i_IBUF[4] w_addr_i_IBUF[3] w_addr_i_IBUF[2] w_addr_i_IBUF[1] w_addr_i_IBUF[0] -autobundled
netbloc @w_addr_i_IBUF,w_addr_h_IBUF 1 3 1 740 3120n
levelinfo -pg 1 0 50 230 590 1610 3360 5070 5320
levelinfo -hier u_relu_activation * 1770 2130 *
pagesize -pg 1 -db -bbox -sgen -170 0 6170 9620
pagesize -hier u_relu_activation -db -bbox -sgen 1610 548 2370 6918
show
zoom 0.0729097
scrollpos -54 -65
#
# initialize ictrl to current module bitserial_nn work:bitserial_nn:NOFILE
ictrl init topinfo |
