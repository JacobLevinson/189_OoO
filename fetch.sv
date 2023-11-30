`timescale 1ns/1ps

import typedefs::fetchStruct; // Importing in CUS instead of module header because only 2005 support :(
module fetch(
input logic clk,
input logic [31:0] pc,
output fetchStruct fd_reg
);

logic [7:0] irom [127:0]; // Generate a ROM to store instructions that will be run

integer i;
initial begin // Simulation construct: Read data from file into ROM
	for (i = 0; i < 127; i = i + 1) begin // Initialize IROM
		irom[i] = '0;
	end
	
	$readmemh("r-test-hex.txt", irom); // REPLACE WITH INSTRUCTION FILE FOR SIMULATION
end

always_ff @(posedge clk) begin
	if(pc + 4 < 127) begin // Both instructions exist
		fd_reg.inst_a 	<= irom[pc];
      fd_reg.inst_b 	<= irom[pc+4];
		fd_reg.pc_a 	<= pc;
		fd_reg.pc_b 	<= pc + 32'd4;
   end else begin // We are out of instructions
		fd_reg.inst_a 	<= 32'd0;
      fd_reg.inst_b 	<= 32'd0;
		fd_reg.pc_a 	<= pc;
		fd_reg.pc_b 	<= pc + 32'd4;
   end
end

endmodule