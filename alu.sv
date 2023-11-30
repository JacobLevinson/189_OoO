`timescale 1ns/1ps

import typedefs::aluStruct;
module alu (
input clk,
input aluStruct aluIn,
output logic [31:0] alu_out,
output logic flag_sign, // Don't need to define a struct for the output because we won't use the flags in this project b/c no branching
output logic flag_zero
);

// Declare local nets
logic [31:0] result;
logic zero;
logic sign;

// LUT for 4-bit ALU control signal
parameter op_and 	= 4'b0000;
parameter op_or 	= 4'b0001;
parameter op_add 	= 4'b0010;
parameter op_sub 	= 4'b0110;
parameter op_xor 	= 4'b0011;
parameter op_sra	= 4'b1110;

logic inA, inB;
assign inA = aluIn.rs1;
assign inB = aluIn.ALUSrc ? aluIn.imm : aluIn.rs2;

always_comb begin
	unique case (aluIn.ALU_ctrl)
		op_and: begin 	
			result = inA & inB; // Use bit-wise operator
			zero = ((inA & inB) == 0);
			sign = ((inA & inB) < 0);
		end
		op_or: begin
			result = inA | inB; // Use bit-wise operator
			zero = ((inA | inB) == 0);
			sign = ((inA | inB) < 0);
		end
		op_add: begin
			result = inA + inB;
			zero = ((inA + inB) == 0);
			sign = ((inA + inB) < 0);
		end
		op_sub: begin
			result = inA - inB;
			zero = ((inA - inB) == 0);
			sign = ((inA - inB) < 0);
		end
		op_xor: begin
			result = inA ^ inB; // Use bit-wise operator
			zero = ((inA ^ inB) == 0);
			sign = ((inA ^ inB) < 0);
		end
		op_sra: begin
			result = inA >>> inB;
			zero = ((inA >>> inB) == 0);
			sign = ((inA >>> inB) < 0);
		end
		default: begin
			result = inA;
			zero = 1;
			sign = 1;
		end
	endcase
end

always_ff @ (posedge clk) begin // Push results to registers
	alu_out 		<= result;
	flag_zero 	<= zero;
	flag_sign 	<= sign;
end

// Check that we don't ever get into the default case
property exclusive_flag;
	@ (posedge clk)
	(zero && sign);
endproperty

assert property (exclusive_flag);

endmodule	