`timescale 1ns/1ps

import typedefs::aluStruct;
import typedefs::fetchStruct;
import typedefs::dispatchStruct;
import typedefs::forwardingStruct;
import typedefs::fuRdyStruct;
import typedefs::memReadInputStruct;
import typedefs::memReadOutputStruct;
import typedefs::robDispatchStruct;




module reservationStation (
    input logic clk,
	input dispatchStruct dispatchData,
	input logic [63:0] retireRegReady, // bit is 1 if we want to mark reg as ready after retire
	input forwardingStruct completeForward,
	input fuRdyStruct fuRdy,
	output memReadInputStruct memReadInput,
	input memReadOutputStruct memReadOutput,
	input logic [15:0] robFree,
	output robDispatchStruct robDispatch
);
logic [63:0] [31:0] physReg = 0;
logic [3:0] firstRobFree;
logic [3:0] secondRobFree;
logic [3:0] robFreeSpace;


reservationStationEntry reservationTable [15:0];
logic [3:0] reservationIndex = 0;

logic [15:0] readyTable = 16'b1111111111111111;

always_ff @(posedge clk) begin

	// Dsipatch stage

	// If we have a valid instruction, dispatch it to the reservation station

	// Check if there is at least 2 free spots in the ROB by checking if there's at least 2 1's in robFree

//	if($countones(robFree) < 2) begin // or other stall signals, we will wrap the rest of our code in this if statement
//		//STALL
//	end
	
	// Find the first free spot in ROB
	// Find the MSB that is set to 1
	automatic integer temp = 0;
	for (int i = 15; i >= 0; i--) begin
		if (robFree[i] == 1'b1) begin
			firstRobFree <= i[3:0];
			temp = i[3:0];
			break;
		end
	end
	// Find the second free spot in ROB
	// Find the second MSB that is set to 1
	for (int i = temp - 1; i >= 0; i--) begin
		if (robFree[i] == 1'b1) begin
			secondRobFree <= i[3:0];
			break;
		end
	end


	// Dispatch the first instruction to the ROB and to the reservation station
	if(dispatchData.inst1valid) begin
		robDispatch.destReg1 <= dispatchData.inst1.rd;
		robDispatch.destRegOld1 <= dispatchData.destRegOld1;
		robDispatch.robNum1 <= firstRobFree;
		robDispatch.pc1 <= dispatchData.inst1.pc;
		robDispatch.valid1 <= 1;
		// Now dispatch to reservation station
		
		
	end else begin
		robDispatch.valid1 <= 0;
	end
	// Dispatch the second instruction to the ROB and to the reservation station
	if(dispatchData.inst2valid) begin
		robDispatch.destReg2 <= dispatchData.inst2.rd;
		robDispatch.destRegOld2 <= dispatchData.destRegOld2;
		robDispatch.robNum2 <= secondRobFree;
		robDispatch.pc2 <= dispatchData.inst2.pc;
		robDispatch.valid2 <= 1;
		// Now dispatch to reservation station
		
	end else begin
		robDispatch.valid2 <= 0;
	end

	


	// Forward outputs from complete stage to waiting registers and mark them as ready
	if(completeForward.valid1) begin
		physReg [completeForward.reg1] <= completeForward.val1;
		reservationTable [completeForward.reg1].src1rdy <= 1;
	end
	if(completeForward.valid2) begin
		physReg [completeForward.reg2] <= completeForward.val2;
		reservationTable [completeForward.reg2].src2rdy <= 1;
	end













end




endmodule