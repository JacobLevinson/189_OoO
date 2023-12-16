`timescale 1ns/100ps

module fetch import typedefs::fetchStruct; (
input logic clk,
input logic [31:0] pc,
input reset,
output fetchStruct fd_reg
);

logic [7:0] irom [127:0]; // Generate a ROM to store instructions that will be run

integer i;
initial begin // Simulation construct: Read data from file into ROM
	for (i = 0; i < 128; i = i + 1) begin // Initialize IROM
		irom[i] = '0;
	end
	
	$readmemh("r-test-hex.txt", irom); // REPLACE WITH INSTRUCTION FILE FOR SIMULATION
end

always_ff @(posedge clk) begin
    if (reset) begin // When in reset, zero everything
        fd_reg.inst_a 	<= '0;
        fd_reg.inst_b 	<= '0;
        fd_reg.pc_a 	<= '0;
        fd_reg.pc_b 	<= '0;   
    end else begin
        if (pc + 4 < 128) begin // Both instructions exist
            fd_reg.inst_a[7:0] 	    <= irom[pc+3]; // Inverted order because instr LSB is the MSB in IROM
            fd_reg.inst_a[15:8]     <= irom[pc+2];
            fd_reg.inst_a[23:16]    <= irom[pc+1];
            fd_reg.inst_a[31:24]    <= irom[pc];
            fd_reg.inst_b[7:0] 	    <= irom[pc+7];
            fd_reg.inst_b[15:8]     <= irom[pc+6];
            fd_reg.inst_b[23:16]    <= irom[pc+5];
            fd_reg.inst_b[31:24]    <= irom[pc+4];
            fd_reg.pc_a 	        <= pc;
            fd_reg.pc_b 	        <= pc + 32'd4;
       end else begin // We are out of instructions
            fd_reg.inst_a 	<= 32'd0;
            fd_reg.inst_b 	<= 32'd0;
            fd_reg.pc_a 	<= pc;
            fd_reg.pc_b 	<= pc + 32'd4;
       end
    end
end

endmodule