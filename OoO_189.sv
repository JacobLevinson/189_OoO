`timescale 1ns/100ps

module OoO_189(
output logic clk,
output logic reset
);
import typedefs::*; 

initial begin
	clk = 0;
	repeat(3) begin
	   reset = 1;
	   #10 clk = !clk;
	end
	forever begin // Apparently we can't use forever loops??
		reset = 0;
		#10 clk = !clk;
		if (pc > 120) begin // Stop the simulation after the PC gets sufficiently large
		  $stop;
		end
	end
end

logic [31:0] pc; // Global PC, no jumping

always_ff @ (negedge clk) begin // Increment PC on the falling edge so signal is stable when read by fetch stage
    if (reset) begin
        pc <= '0;
    end else begin
	   pc <= pc + 32'd8; // Incrememnt by 2 instructions because 2-issue
	end
end


fetchStruct fd_reg; // Pipeline Register
fetch F_STAGE(.clk, .pc, .reset, .fd_reg);

instStruct rename_reg_a; // Pipeline Register
instStruct rename_reg_b; // Pipeline Register
decode DE_STAGE(.clk, .fd_reg, .reset, .rename_reg_a, .rename_reg_b);

dispatchStruct dispatch_reg_a; // Pipeline Register
dispatchStruct dispatch_reg_b; // Pipeline Register
rename RE_STAGE(.clk, .reset, .rename_reg_a, .rename_reg_b, .dispatch_reg_a, .dispatch_reg_b);

rsEntry rsLine_a; // Wire to RS
rsEntry rsLine_b; // Wire to RS
logic[63:0] phy_reg_rdy; // Wire to RS
dispatch DI_STAGE(.clk, .reset, .dispatch_reg_a, .dispatch_reg_b, .rsLine_a, .rsLine_b, .phy_reg_rdy);

regReqStruct reg_request [2:0];
regRespStruct reg_response [2:0];
regfile REGISTERS(.clk, .reset, .request_a(reg_request[0]), .request_b(reg_request[1]), .request_c(reg_request[2]), 
                  .response_a(reg_response[0]), .response_b(reg_response[1]), .response_c(reg_response[2]));

fuRdyStruct fuRdy; // TO DO: IMPLEMENT CONTROL LOGIC FOR THIS TABLE IN TOP LEVEL
rsIssue issue0;
rsIssue issue1;
rsIssue issue2;
reservationStation RS_STAGE(.clk, .reset, .rsLine_a, .rsLine_b, .phy_reg_rdy, .fuRdy, 
                            .reg_request, .reg_response, .issue0, .issue1, .issue2);

memReqStruct request;
memRespStruct response;

mainMem MEMORY(.clk, .reset, .request, .response);

completeStruct complete0;
completeStruct complete1;
completeStruct complete2;
fus IS_STAGE(.clk, .issue0, .issue1, .complete0, .complete1, .issue2, .request, .response, .complete2);
/*
parameter ROB_SIZE_BITS = 4;

typedef struct {
    logic use;
    instStruct instruction;
    logic src1rdy;
    logic src2rdy;
    logic src2rdy;
    logic [1:0] fu;
    logic [ROB_SIZE_BITS-1:0] robNum;
} reservationStationEntry;

typedef struct {
    logic valid1;
    logic valid2;
    logic [5:0] reg1;
    logic [5:0] reg2;
    logic [31:0] val1;
    logic [31:0] val2;
} forwardingStruct;

typedef struct {
    logic [5:0] destReg1;
    logic [5:0] destRegOld1;
    logic [5:0] robNum1;
    logic [31:0] pc1;
    logic valid1;
    logic [5:0] destReg2;
    logic [5:0] destRegOld2;
    logic [5:0] robNum2;
    logic [31:0] pc2;
    logic valid2;
} robDispatchStruct;
*/

endmodule