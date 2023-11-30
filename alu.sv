module alu(
input logic [31:0] rs1,
input logic [31:0] rs2,
input logic [31:0] imm, 
input logic [3:0] ALU_ctrl,
input logic ALUSrc,
output logic [31:0] alu_out,
output logic flag_sign,
output logic flag_zero
);

// LUT for 4-bit ALU control signal
parameter op_and 	= 4'b0000;
parameter op_or 	= 4'b0001;
parameter op_add 	= 4'b0010;
parameter op_sub 	= 4'b0110;
parameter op_xor 	= 4'b0011;
parameter op_sra	= 4'b1110;

logic inA, inB;
assign inA = rs1;
assign inB = ALUSrc ? imm : rs2;

always_comb begin
	unique case (ALU_ctrl)
		op_and: begin 	
			alu_out = inA & inB; // Use bit-wise operator
			flag_zero = ((inA & inB) == 0);
			flag_sign = ((inA & inB) < 0);
		end
		op_or: begin
			alu_out = inA | inB; // Use bit-wise operator
			flag_zero = ((inA | inB) == 0);
			flag_sign = ((inA | inB) < 0);
		end
		op_add: begin
			alu_out = inA + inB;
			flag_zero = ((inA + inB) == 0);
			flag_sign = ((inA + inB) < 0);
		end
		op_sub: begin
			alu_out = inA - inB;
			flag_zero = ((inA - inB) == 0);
			flag_sign = ((inA - inB) < 0);
		end
		op_xor: begin
			alu_out = inA ^ inB; // Use bit-wise operator
			flag_zero = ((inA ^ inB) == 0);
			flag_sign = ((inA ^ inB) < 0);
		end
		op_sra: begin
			alu_out = inA >>> inB;
			flag_zero = ((inA >>> inB) == 0);
			flag_sign = ((inA >>> inB) < 0);
		end
		default: begin
			alu_out = inA;
			flag_zero = 1;
			flag_sign = 1;
		end
	endcase
end

// Check that we don't ever get into the default case
property exclusive_flag;
	(flag_zero && flag_sign);
endproperty

assert property (exclusive_flag);

endmodule	