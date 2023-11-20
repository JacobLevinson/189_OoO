`timescale 1ns/100ps

module rename (
input logic clk,
input logic reset;
);

input logic [4:0] rd_a;
input logic [4:0] rs1_a;
input logic [4:0] rs2_a;

input logic [4:0] rd_b;
input logic [4:0] rs1_b;
input logic [4:0] rs2_b;

output logic [5:0] rd_a_out;
output logic [5:0] rs1_a_out;
output logic [5:0] rs2_a_out;

output logic [5:0] rd_b_out;
output logic [5:0] rs1_b_out;
output logic [5:0] rs2_b_out;

logic wen;
assign wen = 1;

// Declare the register alias table
logic [5:0] rat [31:0];
logic [5:0] rat_ptr;

// Declare the free_pool table
logic [63:0] free_pool; 
logic [5:0] free_pool_ptr;

integer i;
integer j;

always_ff @ (posedge reset) begin
	for (i = 0; i < 32; i = i + 1) begin
		rat[i] = i;
	end
	for (j = 0; j < 64; j = j + 1) begin
		free_pool[j] = (j < 32) ? 0 : 1;
	end
end	

always_ff @ (posedge clk) begin
	if (wen) begin
		rs1_a_out 						<= rat[rs1_a_int];
		rs2_a_out 						<= rat[rs2_a_int];
		rd_a_out 						<= free_pool_ptr;
		// Update tables
		free_pool[free_pool_ptr] 	<= 0;
		free_pool_ptr 					<= free_pool_ptr + 1'b1;
		rat[rd_a] 						<= rd_a_out;
	end
end

always_ff @ (negedge clk) begin
	if (wen) begin
		rs1_b_out 						<= rat[rs1_b_int];
		rs2_b_out 						<= rat[rs2_b_int];
		rd_b_out 						<= free_pool_ptr;
		// Update tables
		free_pool[free_pool_ptr] 	<= 0;
		free_pool_ptr 					<= free_pool_ptr + 1'b1;
		rat[rd_b] 						<= rd_b_out;
	end
end

endmodule

