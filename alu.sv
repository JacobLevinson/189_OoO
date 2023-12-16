`timescale 1ns/100ps

module alu import typedefs::*;(
input logic clk,
input aluInStruct aluIn,
output aluOutStruct aluOut
);

// Declare local nets
logic [31:0] result;
logic zero;
logic sign;

// LUT for 4-bit ALU control signal
parameter ctrl_and 	= 4'b0000;
parameter ctrl_or 	= 4'b0001;
parameter ctrl_add 	= 4'b0010;
parameter ctrl_sub 	= 4'b0110;
parameter ctrl_xor 	= 4'b0011;
parameter ctrl_sra	= 4'b1110;

logic inA, inB;
assign inA = aluIn.rs1;
assign inB = aluIn.ALUSrc ? aluIn.imm : aluIn.rs2;

always_comb begin
	unique case (aluIn.ALUCtrl)
		ctrl_and: begin 	
			result = inA & inB; // Use bit-wise operator
			zero = ((inA & inB) == 0);
			sign = ((inA & inB) < 0);
		end
		ctrl_or: begin
			result = inA | inB; // Use bit-wise operator
			zero = ((inA | inB) == 0);
			sign = ((inA | inB) < 0);
		end
		ctrl_add: begin
			result = inA + inB;
			zero = ((inA + inB) == 0);
			sign = ((inA + inB) < 0);
		end
		ctrl_sub: begin
			result = inA - inB;
			zero = ((inA - inB) == 0);
			sign = ((inA - inB) < 0);
		end
		ctrl_xor: begin
			result = inA ^ inB; // Use bit-wise operator
			zero = ((inA ^ inB) == 0);
			sign = ((inA ^ inB) < 0);
		end
		ctrl_sra: begin
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

always_comb begin
	aluOut.result 	   = result;
	aluOut.flag_zero   = zero;
	aluOut.flag_sign   = sign;
	aluOut.valid       = aluIn.valid;
end

// Check that we don't ever get into the default case
property exclusive_flag;
	@(posedge clk) disable iff (!aluIn.valid)
	!(zero && sign);
endproperty

assert property (exclusive_flag);

endmodule	