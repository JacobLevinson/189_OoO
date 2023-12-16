`timescale 1ns/100ps

module regfile import typedefs::*; ( // Three ports for three issue, may need to expand later to 5 or 6 port
input logic clk,
input logic reset,

input regReqStruct request_a,
input regReqStruct request_b,
input regReqStruct request_c,

output regRespStruct response_a,
output regRespStruct response_b,
output regRespStruct response_c
);

// Local signals
logic RegWrite_a;
logic RegWrite_b;
logic RegWrite_c;

logic [6:0] rs1_a;
logic [6:0] rs1_b;
logic [6:0] rs1_c;

logic [6:0] rs2_a;
logic [6:0] rs2_b;
logic [6:0] rs2_c;

logic [6:0] rd_a;
logic [6:0] rd_b;
logic [6:0] rd_c;

logic [31:0] wr_data_a;
logic [31:0] wr_data_b;
logic [31:0] wr_data_c;

// Parse structs into local signals
assign RegWrite_a = request_a.RegWrite;
assign RegWrite_b = request_b.RegWrite;
assign RegWrite_c = request_c.RegWrite;

assign rs1_a = request_a.rs1;
assign rs1_b = request_b.rs1;
assign rs1_c = request_c.rs1;

assign rs2_a = request_a.rs2;
assign rs2_b = request_b.rs2;
assign rs2_c = request_c.rs2;

assign rd_a = request_a.rd;
assign rd_b = request_b.rd;
assign rd_c = request_c.rd;

assign wr_data_a = request_a.wr_data;
assign wr_data_b = request_b.wr_data;
assign wr_data_c = request_c.wr_data;

// Declare Regfile
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
			if (rd_a != '0) begin // Prevent writing to x0
				registers[rd_a] <= wr_data_a;
			end
		end
		
		// Port b
		if (RegWrite_b) begin
			if (rd_b != '0) begin // Prevent writing to x0
				registers[rd_b] <= wr_data_b;
			end
		end
		
		// Port c
		if (RegWrite_c) begin
			if (rd_b != '0) begin // Prevent writing to x0
				registers[rd_b] <= wr_data_c;
			end
		end
	end
end

always_comb begin // Non-clocked reads, need to put reads into registers on the other side of this port
    response_a.rs1_data = registers[rs1_a];
    response_a.rs2_data = registers[rs2_a];
    response_b.rs1_data = registers[rs1_b];
	response_b.rs2_data = registers[rs2_b];
	response_c.rs1_data = registers[rs1_c];
    response_c.rs2_data = registers[rs2_c];  
end

// Physical register 0 must always be tied to ground
property reg0_ground;
	@(posedge clk) 
	(registers[0] == '0);
endproperty

assert property (reg0_ground);

// Request port a is not wired to a commit stage and should only read
property req_a_read_only;
    @(posedge clk)
    (RegWrite_a == '0);
endproperty

assert property(req_a_read_only);

// Request port b is not wired to a commit stage and should only read
property req_b_read_only;
    @(posedge clk)
    (RegWrite_b == '0);
endproperty

assert property(req_b_read_only);

// Request port c is not wired to a commit stage and should only read
property req_c_read_only;
    @(posedge clk)
    (RegWrite_c == '0);
endproperty

assert property(req_c_read_only);

endmodule
		
		
