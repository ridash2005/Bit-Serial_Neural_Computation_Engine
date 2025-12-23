create_clock -name clk -period 8.000 [get_ports clk] 
set_input_delay 0.5 -clock [get_clocks clk] [get_ports {data_in data_in_valid start w_wr_en w_addr_h w_addr_i w_data rst_n}]
set_output_delay 0.5 -clock [get_clocks clk] [all_outputs]
#phys_opt_design -directive AggressiveHoldFix   <--  for hold timig fix 



