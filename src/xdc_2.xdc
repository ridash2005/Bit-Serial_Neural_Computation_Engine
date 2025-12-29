create_clock -name clk -period 10.000 [get_ports clk] 
set_input_delay 0.5 -clock [get_clocks clk] [all_inputs]
set_output_delay 0.5 -clock [get_clocks clk] [all_outputs]
#phys_opt_design -directive AggressiveHoldFix   <--  for hold timig fix 



