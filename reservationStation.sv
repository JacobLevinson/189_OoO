module reservationStation (
    input logic clk,
	input dispatchStruct dispatchData,
	input logic [63:0] retireRegReady, //bit is 1 if we want to mark reg as ready after retire
	input forwardingStruct completeForward,
	input fuRdyStruct fuRdy,
	output memReadInputStruct memReadInput,
	input memReadOutputStruct memReadOutput
);
logic [63:0] archReg [31:0];





endmodule