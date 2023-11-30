`timescale 1ns/100ps

module rename (
input logic clk,
input logic reset,

input logic [6:0] opcode_a,

input logic [4:0] rd_a_arch,
input logic [4:0] rs1_a_arch,
input logic [4:0] rs2_a_arch,

input logic [6:0] opcode_b,

input logic [4:0] rd_b_arch,
input logic [4:0] rs1_b_arch,
input logic [4:0] rs2_b_arch,

output logic [5:0] rd_a_phy,
output logic [5:0] rs1_a_phy,
output logic [5:0] rs2_a_phy,

output logic [5:0] rd_b_phy,
output logic [5:0] rs1_b_phy,
output logic [5:0] rs2_b_phy
);

parameter i_type 	= 7'b0010011;
parameter lw 		= 7'b0000011;
parameter sw 		= 7'b0100011;

// Declare the register alias table
logic [5:0] rat [31:0];
logic [5:0] rat_ptr;

// Declare the free_pool table, implemented as a circular queue
logic [5:0] free_pool [63:0]; 
logic [5:0] free_pool_ptr_head;
logic [5:0] free_pool_ptr_tail;

logic [1:0] free_pool_ptr_incr; // Detects if we don't need to assign an rd register
assign free_pool_ptr_incr = {((opcode_a == sw) || (rd_a_arch == '0)), ((opcode_b == sw) || (rd_b_arch == '0))};

always_comb begin // NOTE: Need to account for SW instructions which do not have an rd register!
	rs1_a_phy 	= rat[rs1_a_arch];
	
	if (opcode_a == i_type || opcode_a == lw) begin // No rs2;
		rs2_a_phy = '0;
	end else begin 
		rs2_a_phy 	= rat[rs2_a_arch];
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
			rd_a_phy	= '0;
			rd_b_phy	= '0;
		end
		2'b10: begin // A is a SW or x0, B has a valid rd
			rd_a_phy = '0;
			rd_b_phy = free_pool[free_pool_ptr_head];
		end
		2'b01: begin // B is a SW or x0, A has a valid rd
			rd_a_phy = free_pool[free_pool_ptr_head];
			rd_b_phy	= '0;
		end
		2'b00: begin // Neither A or B are SW or x0
			rd_a_phy = free_pool[free_pool_ptr_head];
			rd_b_phy = free_pool[free_pool_ptr_head + 6'b1];
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

endmodule