# Bit-Serial_Neural_Computation_Engine


This repo contains five basic modules:

1)bitserial_nn.sv

2)input_buffer.sv

3)mac_engine.sv

4)relu_activation.sv

5)wmem_hidden.sv

>bitserial_nn.sv contains the overall structure of our neural computation engine.In this module we instantiate all other modules -- input_buffer,mac_engine,relu_activation and wmem_hidden.

>input_buffer.sv describes how input data is packed and stored in a 1D array like structure which is then passed on to the mac_engine.

>wmem_hidden.sv describes how weight data of neuron is stored in a BRAM structure (as coded) and passed on to MAC engine.

>mac_engine.sv module describes how it takes weight data and input_data as inputs and performs multiplication operation on them bit by bit and produces some result after some cycles.

>relu_activation.sv module describes just like a relu activation layer in a neural network how such thing can be implemented in hardware fpgas.The output from the mac_engine is passed on to the relu_activation layer.

## all the files and architecture details will be added soon 
# Stay Tuned !!
