`timescale 1ns/100ps

import typedefs::instStruct;
import typedefs::dispatchStruct;
module rename (
input logic clk,
input logic reset,
input instStruct dec_ren_reg_a,
input instStruct dec_ren_reg_b,
//input logic [5:0] free_reg_a, // Note: Need to code this logic still
//input logic [5:0] free_reg_b,
output dispatchStruct ren_disp_reg_a,
output dispatchStruct ren_disp_reg_b
);

// Local input variables
logic [6:0] opcode_a;
logic [4:0] rd_a_arch;
logic [4:0] rs1_a_arch;
logic [4:0] rs2_a_arch;

assign opcode_a	= dec_ren_reg_a.opcode;
assign rd_a_arch	= dec_ren_reg_a.rd;
assign rs1_a_arch = dec_ren_reg_a.rs1;
assign rs2_a_arch = dec_ren_reg_a.rs2;

logic [6:0] opcode_b;
logic [4:0] rd_b_arch;
logic [4:0] rs1_b_arch;
logic [4:0] rs2_b_arch;

assign opcode_b	= dec_ren_reg_b.opcode;
assign rd_b_arch	= dec_ren_reg_b.rd;
assign rs1_b_arch = dec_ren_reg_b.rs1;
assign rs2_b_arch = dec_ren_reg_b.rs2;

// Local output variables
logic [5:0] rd_a_phy;
logic [5:0] rd_a_phy_old;
logic [5:0] rs1_a_phy;
logic [5:0] rs2_a_phy;

logic [5:0] rd_b_phy;
logic [5:0] rd_b_phy_old;
logic [5:0] rs1_b_phy;
logic [5:0] rs2_b_phy;

// Instruction LUT
localparam i_type	= 7'b0010011;
localparam lw		= 7'b0000011;
localparam sw 		= 7'b0100011;

// Declare the register alias table
logic [5:0] rat [31:0];
logic [5:0] rat_ptr;

// Declare the free_pool table, implemented as a circular queue
logic [5:0] free_pool [63:0]; 
logic [5:0] free_pool_ptr_head;
logic [5:0] free_pool_ptr_tail;

logic [1:0] free_pool_ptr_incr; // Detects if we don't need to assign an rd register
assign free_pool_ptr_incr = {((opcode_a == sw) || (rd_a_arch == '0)), ((opcode_b == sw) || (rd_b_arch == '0))};

always_comb begin // Need to account for SW instructions which do not have an rd register!
	rs1_a_phy 	= rat[rs1_a_arch];
	
	if (opcode_a == i_type || opcode_a == lw) begin // No rs2;
		rs2_a_phy = '0;
	end else begin 
		rs2_a_phy = rat[rs2_a_arch];
	end
	
	// If we have a dependency of instruction b on instruction a
	if (opcode_a == sw) begin
		if (rd_a_arch == rs1_b_arch) begin // Incorrect dependency, there is no rd in the previous instruction
			rs1_b_phy = rat[rs1_b_arch];
		end else begin // No dependency
			rs1_b_phy = rat[rs1_b_arch];
		end	
	end else begin
		if (rd_a_arch == rs1_b_arch) begin // Correct dependency, there was an rd in the previous istruction
			rs1_b_phy = free_pool_ptr_head;
		end else begin // No dependency
			rs1_b_phy = rat[rs1_b_arch];
		end	
	end
	
	if (opcode_b == i_type || opcode_b == lw) begin // There is no rs2 in i_type and lw instructions
		rs2_b_phy = '0;
	end else if (opcode_a == sw) begin
		if (rd_a_arch == rs2_b_arch) begin // Incorrect dependency, there is no rd in the previous instruction
			rs2_b_phy = rat[rs2_b_arch];
		end else begin // No dependency
			rs2_b_phy = rat[rs2_b_arch];
		end
	end else begin // All other isntructions
		if (rd_a_arch == rs2_b_arch) begin
			rs2_b_phy = free_pool_ptr_head;
		end else begin
			rs2_b_phy = rat[rs2_b_arch];
		end
	end
	
	// If we have a store word, then we won't have an rd
	unique case (free_pool_ptr_incr) 
		2'b11: begin // Both A and B are SW or x0
			rd_a_phy			= '0;
			rd_a_phy_old 	= '0;
			rd_b_phy			= '0;
			rd_b_phy_old 	= '0;
		end
		2'b10: begin // A is a SW or x0, B has a valid rd
			rd_a_phy 		= '0;
			rd_a_phy_old 	= '0;
			rd_b_phy 		= free_pool[free_pool_ptr_head];
			rd_b_phy_old 	= rat[rd_b_arch];
		end
		2'b01: begin // B is a SW or x0, A has a valid rd
			rd_a_phy 		= free_pool[free_pool_ptr_head];
			rd_a_phy_old 	= rat[rd_a_arch];
			rd_b_phy			= '0;
			rd_b_phy_old 	= '0;
		end
		2'b00: begin // Neither A or B are SW or x0
			rd_a_phy 		= free_pool[free_pool_ptr_head];
			rd_a_phy_old 	= rat[rd_a_arch];
			rd_b_phy 		= free_pool[free_pool_ptr_head + 6'b1];
			rd_b_phy_old 	= rat[rd_b_arch];
		end
	endcase
end

integer i;
integer j;

always_ff @ (posedge clk) begin
	if (reset) begin // Resets the RAT and free pool tables
		for (i = 0; i < 32; i = i + 1) begin
			rat[i] <= i;
		end
		
		for (j = 0; j < 32; j = j + 1) begin
			free_pool[j] <= j + 6'd32;
		end
		for (j = 32; j < 64; j = j + 1) begin
			free_pool[j] <= '0;
		end
		
		free_pool_ptr_head <= 0; 
		free_pool_ptr_tail <= 32;
	end else begin
		unique case (free_pool_ptr_incr) 
			2'b11: begin // Both A and B are SW or x0
				// No changes to RAT or free pool
			end
			2'b10: begin // A is a SW or x0, B has a valid rd
				rat[rd_b_arch] 								<= free_pool[free_pool_ptr_head]; 
				free_pool[free_pool_ptr_head] 			<= '0;
				free_pool_ptr_head							<= free_pool_ptr_head + 6'd1;
			end
			2'b01: begin // B is a SW or x0, A has a valid rd
				rat[rd_a_arch] 								<= free_pool[free_pool_ptr_head]; 
				free_pool[free_pool_ptr_head] 			<= '0;
				free_pool_ptr_head							<= free_pool_ptr_head + 6'd1;
			end
			2'b00: begin // Both are SW
				rat[rd_a_arch]									<= free_pool[free_pool_ptr_head]; 
				rat[rd_b_arch]									<= free_pool[free_pool_ptr_head + 6'd1]; 				
				free_pool[free_pool_ptr_head] 			<= '0;
				free_pool[free_pool_ptr_head + 6'b1] 	<= '0;
				free_pool_ptr_head							<= free_pool_ptr_head + 6'd2;
			end
		endcase
	end
end

always_ff @ (posedge clk) begin // Update pipeline register
	// Pass through, no physical register computation
	ren_disp_reg_a.pc 		<= dec_ren_reg_a.pc;
	ren_disp_reg_a.opcode	<= dec_ren_reg_a.opcode;
	ren_disp_reg_a.funct3	<= dec_ren_reg_a.funct3;
	ren_disp_reg_a.funct7	<= dec_ren_reg_a.funct7;
	ren_disp_reg_a.imm		<= dec_ren_reg_a.imm;
	ren_disp_reg_a.control	<= dec_ren_reg_a.control;
	
	ren_disp_reg_b.pc 		<= dec_ren_reg_b.pc;
	ren_disp_reg_b.opcode	<= dec_ren_reg_b.opcode;
	ren_disp_reg_b.funct3	<= dec_ren_reg_b.funct3;
	ren_disp_reg_b.funct7	<= dec_ren_reg_b.funct7;
	ren_disp_reg_b.imm		<= dec_ren_reg_b.imm;
	ren_disp_reg_b.control	<= dec_ren_reg_b.control;
	
	// Push new physical register addresses to pipeline registers
	ren_disp_reg_a.rd			<= rd_a_phy;
	ren_disp_reg_a.rd_old	<= rd_a_phy_old;
	ren_disp_reg_a.rs1		<= rs1_a_phy;
	ren_disp_reg_a.rs2		<= rs2_a_phy;
	
	ren_disp_reg_b.rd			<= rd_b_phy;
	ren_disp_reg_b.rd_old	<= rd_b_phy_old;
	ren_disp_reg_b.rs1		<= rs1_b_phy;
	ren_disp_reg_b.rs2		<= rs2_b_phy;
end
endmodule