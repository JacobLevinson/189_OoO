/*`timescale 1ns/100ps

module tb_rename();

logic [6:0] opcode_a;

logic [4:0] rd_a_arch;
logic [4:0] rs1_a_arch;
logic [4:0] rs2_a_arch;

logic [6:0] opcode_b;

logic [4:0] rd_b_arch;
logic [4:0] rs1_b_arch;
logic [4:0] rs2_b_arch;

logic [5:0] rd_a_phy;
logic [5:0] rs1_a_phy;
logic [5:0] rs2_a_phy;

logic [5:0] rd_b_phy;
logic [5:0] rs1_b_phy;
logic [5:0] rs2_b_phy;

logic clk;
logic reset;


	always begin
		clk = 0;
		#10;
		clk = 1;
		#10;
	end


initial begin
	reset = 1;
	#10;
	reset = 0;
	#10;
	rd_a_arch = 1;
	rs1_a_arch = 2;
	rs2_a_arch = 3;
	rd_b_arch = 2;
	rs1_b_arch = 1;
	rs2_b_arch = 1;
end

rename DUT(.*);

endmodule*/