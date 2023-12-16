`timescale 1ns/100ps

module mainMem import typedefs::*; (
input logic clk,
input logic reset,
input memReqStruct request, // May need to add more ports for retire stages
output memRespStruct response
);

// Decode structs into local signals
logic [31:0] addr;
logic [31:0] wr_data;
logic MemWrite;
logic MemRead;
logic valid;

assign addr     = request.addr;
assign wr_data  = request.wr_data;
assign MemWrite = request.MemWrite;
assign MemRead  = request.MemRead;
assign valid    = request.valid;

// 32 byte RAM
logic [7:0] dmem [31:0]; 

integer i;
always_ff @ (posedge clk) begin
	if (reset) begin
		for (i = 0; i < 32; i = i + 1) begin
			dmem[i] <= '0;
		end
	end else begin
		if (valid && MemWrite) begin
			dmem[addr[4:0]] 		<= wr_data[7:0];
			dmem[addr[4:0] + 5'd1] 	<= wr_data[15:8];
			dmem[addr[4:0] + 5'd2] 	<= wr_data[23:17];
			dmem[addr[4:0] + 5'd3] 	<= wr_data[31:24];
		end 
	end
end

always_comb begin
    if (valid && MemRead) begin
		response.rd_data[7:0] 	 = dmem[addr[4:0]];
		response.rd_data[15:8]   = dmem[addr[4:0] + 5'd1];
		response.rd_data[23:16]  = dmem[addr[4:0] + 5'd2];
		response.rd_data[31:24]  = dmem[addr[4:0] + 5'd3];
	end else begin // In all cases we are not reading, output zeros
	    response.rd_data[7:0] 	 = '0;
		response.rd_data[15:8]   = '0;
		response.rd_data[23:16]  = '0;
		response.rd_data[31:24]  = '0;
	end
	
	// Pass through signals
	response.MemWrite = MemWrite;
	response.MemRead  = MemRead;
	response.valid    = valid;
end

property single_port_ram; // MemWrite and MemRead may not be asserted together
	@(posedge clk) disable iff (reset)
	(!MemWrite && !MemRead);
endproperty

assert property (single_port_ram);

endmodule