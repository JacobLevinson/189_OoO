`timescale 1ns/100ps

module mainMem import typedefs::*; (
input logic clk,
input logic reset,
input memReqStruct request_a, 
input memReqStruct request_b, 
input memReqStruct request_c, 
output memRespStruct response_a,
output memRespStruct response_b,
output memRespStruct response_c
);

// Decode structs into local signals
logic [31:0] addr_a;
logic [31:0] wr_data_a;
logic MemWrite_a;
logic MemRead_a;
logic valid_a;

logic [31:0] addr_b;
logic [31:0] wr_data_b;
logic MemWrite_b;
logic MemRead_b;
logic valid_b;

logic [31:0] addr_c;
logic [31:0] wr_data_c;
logic MemWrite_c;
logic MemRead_c;
logic valid_c;

assign addr_a     = request_a.addr;
assign wr_data_a  = request_a.wr_data;
assign MemWrite_a = request_a.MemWrite;
assign MemRead_a  = request_a.MemRead;
assign valid_a    = request_a.valid;

assign addr_b     = request_b.addr;
assign wr_data_b  = request_b.wr_data;
assign MemWrite_b = request_b.MemWrite;
assign MemRead_b  = request_b.MemRead;
assign valid_b    = request_b.valid;

assign addr_c     = request_c.addr;
assign wr_data_c  = request_c.wr_data;
assign MemWrite_c = request_c.MemWrite;
assign MemRead_c  = request_c.MemRead;
assign valid_c    = request_c.valid;

// Instantiate 32 byte RAM
logic [7:0] dmem [31:0]; 

integer i;
always_ff @ (posedge clk) begin // Store operations
	if (reset) begin
		for (i = 0; i < 32; i = i + 1) begin
			dmem[i] <= '0;
		end
	end else begin
		if (valid_a && MemWrite_a) begin
			dmem[addr_a[4:0]] 		 <= wr_data_a[7:0];
			dmem[addr_a[4:0] + 5'd1] <= wr_data_a[15:8];
			dmem[addr_a[4:0] + 5'd2] <= wr_data_a[23:17];
			dmem[addr_a[4:0] + 5'd3] <= wr_data_a[31:24];
		end 
		
		if (valid_b && MemWrite_b) begin
			dmem[addr_b[4:0]] 		 <= wr_data_b[7:0];
			dmem[addr_b[4:0] + 5'd1] <= wr_data_b[15:8];
			dmem[addr_b[4:0] + 5'd2] <= wr_data_b[23:17];
			dmem[addr_b[4:0] + 5'd3] <= wr_data_b[31:24];
		end 
		
		if (valid_c && MemWrite_c) begin
			dmem[addr_c[4:0]] 		 <= wr_data_c[7:0];
			dmem[addr_c[4:0] + 5'd1] <= wr_data_c[15:8];
			dmem[addr_c[4:0] + 5'd2] <= wr_data_c[23:17];
			dmem[addr_c[4:0] + 5'd3] <= wr_data_c[31:24];
		end 
	end
end

always_comb begin // Read operations on port a
    if (valid_b && MemRead_b) begin
		response_b.rd_data[7:0]   = dmem[addr_b[4:0]];
		response_b.rd_data[15:8]  = dmem[addr_b[4:0] + 5'd1];
		response_b.rd_data[23:16] = dmem[addr_b[4:0] + 5'd2];
		response_b.rd_data[31:24] = dmem[addr_b[4:0] + 5'd3];
	end else begin // In all cases we are not reading, output zeros
	    response_b.rd_data[7:0]    = '0;
		response_b.rd_data[15:8]   = '0;
		response_b.rd_data[23:16]  = '0;
		response_b.rd_data[31:24]  = '0;
	end
	
	// Pass through signals
	response_b.MemWrite = MemWrite_b;
	response_b.MemRead  = MemRead_b;
	response_b.valid    = valid_b;
end

always_comb begin // Read operations on port b
    if (valid_c && MemRead_c) begin
		response_c.rd_data[7:0]   = dmem[addr_c[4:0]];
		response_c.rd_data[15:8]  = dmem[addr_c[4:0] + 5'd1];
		response_c.rd_data[23:16] = dmem[addr_c[4:0] + 5'd2];
		response_c.rd_data[31:24] = dmem[addr_c[4:0] + 5'd3];
	end else begin // In all cases we are not reading, output zeros
	    response_c.rd_data[7:0]    = '0;
		response_c.rd_data[15:8]   = '0;
		response_c.rd_data[23:16]  = '0;
		response_c.rd_data[31:24]  = '0;
	end
	
	// Pass through signals
	response_c.MemWrite = MemWrite_c;
	response_c.MemRead  = MemRead_c;
	response_c.valid    = valid_c;
end

always_comb begin // Read operations on port c
    if (valid_a && MemRead_a) begin
		response_a.rd_data[7:0]   = dmem[addr_a[4:0]];
		response_a.rd_data[15:8]  = dmem[addr_a[4:0] + 5'd1];
		response_a.rd_data[23:16] = dmem[addr_a[4:0] + 5'd2];
		response_a.rd_data[31:24] = dmem[addr_a[4:0] + 5'd3];
	end else begin // In all cases we are not reading, output zeros
	    response_a.rd_data[7:0]    = '0;
		response_a.rd_data[15:8]   = '0;
		response_a.rd_data[23:16]  = '0;
		response_a.rd_data[31:24]  = '0;
	end
	
	// Pass through signals
	response_a.MemWrite = MemWrite_a;
	response_a.MemRead  = MemRead_a;
	response_a.valid    = valid_a;
end

property single_port_ram_a; // MemWrite and MemRead may not be asserted together
	@(posedge clk) disable iff (reset)
	(!MemWrite_a && !MemRead_a);
endproperty

assert property (single_port_ram_a);

property single_port_ram_b; // MemWrite and MemRead may not be asserted together
	@(posedge clk) disable iff (reset)
	(!MemWrite_b && !MemRead_b);
endproperty

assert property (single_port_ram_c);

property single_port_ram_c; // MemWrite and MemRead may not be asserted together
	@(posedge clk) disable iff (reset)
	(!MemWrite_c && !MemRead_c);
endproperty

assert property (single_port_ram_c);

endmodule