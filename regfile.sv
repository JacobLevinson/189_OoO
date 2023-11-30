module regfile (
input logic clk,
input logic RegWrite_a,
input logic RegWrite_b,
input logic reset,

input logic [6:0] rd_addr_a1,
input logic [6:0] rd_addr_a2,
input logic [6:0] wr_addr_a,

input logic [6:0] rd_addr_b1,
input logic [6:0] rd_addr_b2,
input logic [6:0] wr_addr_b,

input logic [31:0] wr_data_a,
input logic [31:0] wr_data_b,

output logic [31:0] rd_data_a1,
output logic [31:0] rd_data_a2,

output logic [31:0] rd_data_b1,
output logic [31:0] rd_data_b2
);

logic [31:0] registers [63:0];

integer i;

always_ff @ (posedge clk) begin
	if (reset) begin
		for (i = 0; i < 64; i = i + 1) begin
			registers[i] = '0;
		end
	end else begin
		// Port a
		if (RegWrite_a) begin
			if (wr_addr_a != '0) begin // Prevent writing to x0
				registers[wr_addr_a] <= wr_data_a;
			end
		end
		rd_data_a1 <= registers[rd_addr_a1];
		rd_data_a2 <= registers[rd_addr_a2];
		
		// Port b
		if (RegWrite_b) begin
			if (wr_addr_b != '0) begin // Prevent writing to x0
				registers[wr_data_b] <= wr_data_b;
			end
		end
		rd_data_b1 <= registers[rd_addr_b1];
		rd_data_b2 <= registers[rd_addr_b2];
	end
end

// Physical register 0 must always be tied to ground
property reg0_ground;
	@(posedge clk) 
	(registers[0] == '0);
endproperty

assert property (reg0_ground);

endmodule
		
		
