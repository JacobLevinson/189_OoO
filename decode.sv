`timescale 1ns/100ps

import typedefs::fetch_decode;
import typedefs::ctrlStruct; // Importing in CUS instead of module header because only 2005 support :(
import typedefs::instStruct;
module decode (
input logic clk,
input fetch_decode fd_reg,
output instStruct dec_ren_reg_a,
output instStruct dec_ren_reg_b
);

// Might be smarter to separate the combinational and sequential logic... oops

always_ff @ (posedge clk) begin // Parse instructions
	dec_ren_reg_a.opcode	<= fd_reg.inst_a [6:0];
	dec_ren_reg_a.rd		<= fd_reg.inst_a [11:7];
	dec_ren_reg_a.funct3 <= fd_reg.inst_a [14:12];
	dec_ren_reg_a.rs1    <= fd_reg.inst_a [19:15];
	dec_ren_reg_a.rs2    <= fd_reg.inst_a [24:20];
	dec_ren_reg_a.funct7 <= fd_reg.inst_a [31:25];
	
	dec_ren_reg_b.opcode <= fd_reg.inst_b [6:0];
	dec_ren_reg_b.rd 		<= fd_reg.inst_b [11:7];
	dec_ren_reg_b.funct3 <= fd_reg.inst_b [14:12];
	dec_ren_reg_b.rs1    <= fd_reg.inst_b [19:15];
	dec_ren_reg_b.rs2    <= fd_reg.inst_b [24:20];
	dec_ren_reg_b.funct7 <= fd_reg.inst_b [31:25];
	
	dec_ren_reg_a.pc 		<= fd_reg.pc_a; // These are simply passed through
	dec_ren_reg_b.pc 		<= fd_reg.pc_b;
end

// LUT for ImmGen and Control Signals
localparam i_type = 7'b0010011;
localparam load 	= 7'b0000011;
localparam s_type	= 7'b0100011;
localparam r_type = 7'b0110011;

always_ff @ (posedge clk) begin // ImmGen for inst_a
	case (fd_reg.inst_a [6:0]) 
		i_type: begin 
			dec_ren_reg_a.imm[11:0]		<= fd_reg.inst_a[31:20];
			dec_ren_reg_a.imm[31:12] 	<= 'b0;
		end
		load: begin 
			dec_ren_reg_a.imm[11:0]  	<= fd_reg.inst_a[31:20];
			dec_ren_reg_a.imm[31:12] 	<= 'b0;
		end
		s_type: begin
			dec_ren_reg_a.imm[4:0]   	<= fd_reg.inst_a[11:7];
			dec_ren_reg_a.imm[11:5]  	<= fd_reg.inst_a[31:25];
			dec_ren_reg_a.imm[31:12] 	<= 'b0;
		end
		default:
			dec_ren_reg_a.imm[31:0] 	<= 'b0;
	endcase
end
	
always_ff @ (posedge clk) begin // ImmGen for inst_b
	case (fd_reg.inst_b [6:0]) 
		i_type:  begin
			dec_ren_reg_b.imm[11:0]  	<= fd_reg.inst_b[31:20];
			dec_ren_reg_b.imm[31:12] 	<= 'b0;
		end
		load: begin
			dec_ren_reg_b.imm[11:0]  	<= fd_reg.inst_b[31:20];
			dec_ren_reg_b.imm[31:12] 	<= 'b0;
		end
		s_type: begin
			dec_ren_reg_b.imm[4:0]   	<= fd_reg.inst_b[11:7];
			dec_ren_reg_b.imm[11:5]  	<= fd_reg.inst_b[31:25];
			dec_ren_reg_b.imm[31:12] 	<= 'b0;
		end
		default:
			dec_ren_reg_b.imm[31:0] 	<= 'b0;
	endcase
end

always_ff @ (posedge clk) begin // Generate control signals
	case (fd_reg.inst_a [6:0]) 
		r_type: begin 
			dec_ren_reg_a.control.MemRead 	<= 0;
			dec_ren_reg_a.control.MemtoReg 	<= 0;
			dec_ren_reg_a.control.ALUOp    	<= 2'b10;
			dec_ren_reg_a.control.MemWrite 	<= 0;
			dec_ren_reg_a.control.ALUSrc   	<= 0;
			dec_ren_reg_a.control.RegWrite 	<= 1;
		end
		i_type: begin 
			dec_ren_reg_a.control.MemRead  	<= 0;
			dec_ren_reg_a.control.MemtoReg 	<= 0;
			dec_ren_reg_a.control.ALUOp    	<= 2'b11;
			dec_ren_reg_a.control.MemWrite 	<= 0;
			dec_ren_reg_a.control.ALUSrc   	<= 1;
			dec_ren_reg_a.control.RegWrite 	<= 1;
		end
		load: begin 
			dec_ren_reg_a.control.MemRead  	<= 1;
			dec_ren_reg_a.control.MemtoReg 	<= 1;
			dec_ren_reg_a.control.ALUOp    	<= 2'b00;
			dec_ren_reg_a.control.MemWrite 	<= 0;
			dec_ren_reg_a.control.ALUSrc   	<= 1;
			dec_ren_reg_a.control.RegWrite 	<= 1;
		end
		s_type: begin 
			dec_ren_reg_a.control.MemRead  	<= 0;
			dec_ren_reg_a.control.MemtoReg 	<= 0;
			dec_ren_reg_a.control.ALUOp    	<= 2'b00;
			dec_ren_reg_a.control.MemWrite 	<= 1;
			dec_ren_reg_a.control.ALUSrc   	<= 1;
			dec_ren_reg_a.control.RegWrite 	<= 0;
		end
		default: begin
			dec_ren_reg_a.control.MemRead  	<= 0;
			dec_ren_reg_a.control.MemtoReg 	<= 0;
			dec_ren_reg_a.control.ALUOp    	<= 2'b00;
			dec_ren_reg_a.control.MemWrite 	<= 0;
			dec_ren_reg_a.control.ALUSrc   	<= 0;
			dec_ren_reg_a.control.RegWrite 	<= 0;
		end
	endcase
end
		
always_ff @ (posedge clk) begin // Generate control signals
	case (fd_reg.inst_b [6:0]) 
		r_type: begin 
			dec_ren_reg_b.control.MemRead		<= 0;
			dec_ren_reg_b.control.MemtoReg	<= 0;
			dec_ren_reg_b.control.ALUOp		<= 2'b10;
			dec_ren_reg_b.control.MemWrite	<= 0;
			dec_ren_reg_b.control.ALUSrc		<= 0;
			dec_ren_reg_b.control.RegWrite	<= 1;
		end
		i_type: begin 
			dec_ren_reg_b.control.MemRead		<= 0;
			dec_ren_reg_b.control.MemtoReg	<= 0;
			dec_ren_reg_b.control.ALUOp	   <= 2'b11;
			dec_ren_reg_b.control.MemWrite	<= 0;
			dec_ren_reg_b.control.ALUSrc		<= 1;
			dec_ren_reg_b.control.RegWrite	<= 1;
		end
		load: begin
			dec_ren_reg_b.control.MemRead		<= 1;
			dec_ren_reg_b.control.MemtoReg	<= 1;
			dec_ren_reg_b.control.ALUOp		<= 2'b00;
			dec_ren_reg_b.control.MemWrite	<= 0;
			dec_ren_reg_b.control.ALUSrc	   <= 1;
			dec_ren_reg_b.control.RegWrite	<= 1;
		end
		s_type: begin 
			dec_ren_reg_b.control.MemRead		<= 0;
			dec_ren_reg_b.control.MemtoReg	<= 0;
			dec_ren_reg_b.control.ALUOp		<= 2'b00;
			dec_ren_reg_b.control.MemWrite	<= 1;
			dec_ren_reg_b.control.ALUSrc		<= 1;
			dec_ren_reg_b.control.RegWrite	<= 0;
		end
		default: begin
			dec_ren_reg_b.control.MemRead		<= 0;
			dec_ren_reg_b.control.MemtoReg	<= 0;
			dec_ren_reg_b.control.ALUOp		<= 2'b00;
			dec_ren_reg_b.control.MemWrite	<= 0;
			dec_ren_reg_b.control.ALUSrc		<= 0;
			dec_ren_reg_b.control.RegWrite	<= 0;
		end
	endcase
end
		
endmodule