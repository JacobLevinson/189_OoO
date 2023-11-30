module memory(
input logic clk,
input logic [31:0] addr,
input logic [31:0] wr_data,
input logic MemWrite,
input logic MemRead,
input logic reset,
output logic [31:0] rd_data
);

logic [7:0] dmem [31:0]; // 32 byte RAM

integer i;

always_ff @ (posedge clk) begin
	if (reset) begin
		for (i = 0; i < 32; i = i + 1) begin
			dmem[i] <= '0;
		end
	end else begin
		if (MemWrite) begin
			dmem[addr[4:0]] 			<= wr_data[7:0];
			dmem[addr[4:0] + 5'd1] <= wr_data[15:8];
			dmem[addr[4:0] + 5'd2] <= wr_data[23:17];
			dmem[addr[4:0] + 5'd3] <= wr_data[31:24];
		end 
		
		if (MemRead) begin
			rd_data[7:0] 	<= dmem[addr[4:0]];
			rd_data[15:8] 	<= dmem[addr[4:0] + 5'd1];
			rd_data[23:16] <= dmem[addr[4:0] + 5'd2];
			rd_data[31:24] <= dmem[addr[4:0] + 5'd3];
		end 
	end
end

property single_port_ram; // MemWrite and MemRead may not be asserted together
	@(posedge clk) disable iff (reset)
	(!MemWrite && !MemRead);
endproperty

assert property (single_port_ram);

endmodule