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
		if (pc > 240) begin // Stop the simulation after the PC gets sufficiently large
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

instStruct rename_reg_a; // Wire pipeline Register
instStruct rename_reg_b; // Wire pipeline Register
decode DE_STAGE(.clk, .fd_reg, .reset, .rename_reg_a, .rename_reg_b);

dispatchStruct dispatch_reg_a; // Wire pipeline Register
dispatchStruct dispatch_reg_b; // Wire pipeline Register
freeRegStruct freeReg_a; // Wires from complete stage
freeRegStruct freeReg_b; // Wires from complete stage
rename RE_STAGE(.clk, .reset, .rename_reg_a, .rename_reg_b, .freeReg_a, .freeReg_b, .dispatch_reg_a, .dispatch_reg_b);

regReqStruct reg_request_a; // Request to regile
regReqStruct reg_request_b;
regRespStruct reg_response_a; // Response from regfile
regRespStruct reg_response_b;

forwardingStruct forward_a;
forwardingStruct forward_b;
forwardingStruct forward_c;

rsEntry rsLine_a; // Wire to RS
rsEntry rsLine_b; // Wire to RS
robDispatchStruct robDispatch_a; // Wire to ROB
robDispatchStruct robDispatch_b; // Wire to ROB
dispatch DI_STAGE(.clk, .reset, .dispatch_reg_a, .dispatch_reg_b, .forward_a, .forward_b, .forward_c, .reg_request_a, .reg_request_b, .reg_response_a, .reg_response_b,
                  .rsLine_a, .rsLine_b, .robDispatch_a, .robDispatch_b);

rsIssue issue0;
rsIssue issue1;
rsIssue issue2;
reservationStation RS_STAGE(.clk, .reset, .rsLine_a, .rsLine_b, .forward_a, .forward_b, .forward_c, .issue0, .issue1, .issue2);

completeStruct complete0;
completeStruct complete1;
completeStruct complete2;
fus IS_STAGE(.clk, .issue0, .issue1, .complete0, .complete1, .issue2, .request(memRequest_c), .response(memResponse_c), .complete2);

robEntryStruct retire_instr_a;
robEntryStruct retire_instr_b;
complete_rob C_STAGE(.clk, .reset, .complete0, .complete1, .complete2, .robDispatch_a, .robDispatch_b, 
                     .forward_a, .forward_b, .forward_c, .retire_instr_a, .retire_instr_b);

retire RET_STAGE (.clk, .retire_instr_a, .retire_instr_b, .regReqest_a(reg_request_c), .regReqest_b(reg_request_d), .memRequest_a, .memRequest_b, .freeReg_a, .freeReg_b);

regReqStruct reg_request_c; // Request to regile
regReqStruct reg_request_d;
regRespStruct reg_response_c; // Response from regfile
regRespStruct reg_response_d;
regfile REGISTERS(.clk, .reset, .request_a(reg_request_a), .request_b(reg_request_b), .request_c(reg_request_c), .request_d(reg_request_d),
                  .response_a(reg_response_a), .response_b(reg_response_b), .response_c(reg_response_c), .response_d(reg_response_d));
                  
memReqStruct memRequest_a;              
memReqStruct memRequest_b;
memReqStruct memRequest_c;
memRespStruct memResponse_a;    
memRespStruct memResponse_b;
memRespStruct memResponse_c;
mainMem MEMORY(.clk, .reset, .request_a(memRequest_a), .request_b(memRequest_b), .request_c(memRequest_c),
               .response_a(memResponse_a), .response_b(memResponse_b), .response_c(memResponse_c));

endmodule