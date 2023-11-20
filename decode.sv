`timescale 1ns/100ps

module decode (
input clock, 
input inst_a,
input inst_b
) begin

input logic clock;
input logic [31:0] inst_a;
input logic [31:0] inst_b;

logic [6:0] opcode_a;
logic [4:0] rd_a;
logic [4:0] rs1_a;
logic [4:0] rs2_a;
logic [2:0] funct3_a;
logic [6:0] funct7_a;
logic [31:0] imm_a;

logic [6:0] opcode_b;
logic [4:0] rd_b;
logic [4:0] rs1_b;
logic [4:0] rs2_b;
logic [2:0] funct3_b;
logic [6:0] funct7_b;
logic [31:0] imm_b;

always_comb begin // Registers
	opcode_a = inst_a [6:0];
	rd_a     = inst_a [11:7];
	funct3_a = inst_a [14:12];
	rs1_a    = inst_a [19:15];
	rs2_a    = inst_a [24:20];
	funct7_a = inst_a [31:25];
	
	opcode_b = inst_b [6:0];
	rd_b     = inst_b [11:7];
	funct3_b = inst_b [14:12];
	rs1_b    = inst_b [19:15];
	rs2_b    = inst_b [24:20];
	funct7_b = inst_b [31:25];
end

always_comb begin // ImmGen for inst_a
	case (inst_a [6:0]) begin
		7'b0010011:  // I-type (ALU immediate)
			imm_a[11:0]  = inst_a[31:20];
			imm_a[31:12] = 'b0;
		7'b0000011: // Load
			imm_a[11:0]  = inst_a[31:20];
			imm_a[31:12] = 'b0;
		7'b0100011: // S-type (Store)
			imm_a[4:0]   = inst_a[11:7];
			imm_a[11:5]  = inst_a[31:25];
			imm_a[31:12] = 'b0;
		default:
			imm_a[31:0] = 'b0;
	endcase
end
	
always_comb begin // ImmGen for inst_b
	case (inst_a [6:0]) begin
		7'b0010011:  // I-type (ALU immediate)
			imm_b[11:0]  = inst_b[31:20];
			imm_b[31:12] = 'b0;
		7'b0000011: // Load
			imm_b[11:0]  = inst_b[31:20];
			imm_b[31:12] = 'b0;
		7'b0100011: // S-type (Store)
			imm_b[4:0]   = inst_b[11:7];
			imm_b[11:5]  = inst_b[31:25];
			imm_b[31:12] = 'b0;
		default:
			imm_b[31:0] = 'b0;
	endcase
end

logic MemRead_a;
logic MemtoReg_a;
logic [1:0] ALUOp_a;
logic MemWrite_a;
logic ALUSrc_a;
logic RegWrite_a;

logic MemRead_b;
logic MemtoReg_b;
logic [1:0] ALUOp_b;
logic MemWrite_b;
logic ALUSrc_b;
logic RegWrite_b;

always_comb begin // Generate control signals
	case (inst_a [6:0]) begin
		7'b0110011: // R-type
			MemRead_a  = 0;
			MemtoReg_a = 0;
			ALUOp_a    = 2'b10;
			MemWrite_a = 0;
			ALUSrc_a   = 0;
			RegWrite_a = 1;
		7'b0010011: // I-type
			MemRead_a  = 0;
			MemtoReg_a = 0;
			ALUOp_a    = 2'b11;
			MemWrite_a = 0;
			ALUSrc_a   = 1;
			RegWrite_a = 1;
		7'b0000011: // Load
			MemRead_a  = 1;
			MemtoReg_a = 1;
			ALUOp_a    = 2'b00;
			MemWrite_a = 0;
			ALUSrc_a   = 1;
			RegWrite_a = 1;
		7'b0100011: // S-type (store)
			MemRead_a  = 0;
			MemtoReg_a = 0;
			ALUOp_a    = 2'b00;
			MemWrite_a = 1;
			ALUSrc_a   = 1;
			RegWrite_a = 0;
		default:
			MemRead_a  = 0;
			MemtoReg_a = 0;
			ALUOp_a    = 2'b00;
			MemWrite_a = 0;
			ALUSrc_a   = 0;
			RegWrite_a = 0;
	endcase
end
		
always_comb begin // Generate control signals
	case (inst_b [6:0]) begin
		7'b0110011: // R-type
			MemRead_b  = 0;
			MemtoReg_b = 0;
			ALUOp_b    = 2'b10;
			MemWrite_b = 0;
			ALUSrc_b   = 0;
			RegWrite_b = 1;
		7'b0010011: // I-type
			MemRead_b  = 0;
			MemtoReg_b = 0;
			ALUOp_b    = 2'b11;
			MemWrite_b = 0;
			ALUSrc_b   = 1;
			RegWrite_b = 1;
		7'b0000011: // Load
			MemRead_b  = 1;
			MemtoReg_b = 1;
			ALUOp_b    = 2'b00;
			MemWrite_b = 0;
			ALUSrc_b   = 1;
			RegWrite_b = 1;
		7'b0100011: // S-type (store)
			MemRead_b  = 0;
			MemtoReg_b = 0;
			ALUOp_b    = 2'b00;
			MemWrite_b = 1;
			ALUSrc_b   = 1;
			RegWrite_b = 0;
		default:
			MemRead_b  = 0;
			MemtoReg_b = 0;
			ALUOp_b    = 2'b00;
			MemWrite_b = 0;
			ALUSrc_b   = 0;
			RegWrite_b = 0;
	endcase
end

endmodule
		