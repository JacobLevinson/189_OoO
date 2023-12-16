`timescale 1ns/100ps

module rename import typedefs::*; (
input logic clk,
input logic reset,
input instStruct rename_reg_a,
input instStruct rename_reg_b,
//input logic [5:0] free_reg_a, // Note: Need to code this logic still
//input logic [5:0] free_reg_b,
output dispatchStruct dispatch_reg_a,
output dispatchStruct dispatch_reg_b
);

// Local input variables
logic [6:0] opcode_a;
logic [4:0] rd_a_arch;
logic [4:0] rs1_a_arch;
logic [4:0] rs2_a_arch;
logic [2:0] funct3_a;
logic [6:0] funct7_a;
logic [1:0] ALUOp_a;

assign opcode_a	    = rename_reg_a.opcode;
assign rd_a_arch    = rename_reg_a.rd;
assign rs1_a_arch   = rename_reg_a.rs1;
assign rs2_a_arch   = rename_reg_a.rs2;
assign funct3_a     = rename_reg_a.funct3;
assign funct7_a     = rename_reg_a.funct7;
assign ALUOp_a      = rename_reg_a.control.ALUOp;

logic [6:0] opcode_b;
logic [4:0] rd_b_arch;
logic [4:0] rs1_b_arch;
logic [4:0] rs2_b_arch;
logic [2:0] funct3_b;
logic [6:0] funct7_b;
logic [1:0] ALUOp_b;

assign opcode_b	    = rename_reg_b.opcode;
assign rd_b_arch	= rename_reg_b.rd;
assign rs1_b_arch   = rename_reg_b.rs1;
assign rs2_b_arch   = rename_reg_b.rs2;
assign funct3_b     = rename_reg_b.funct3;
assign funct7_b     = rename_reg_b.funct7;
assign ALUOp_b      = rename_reg_b.control.ALUOp;

// Local output variables
logic [5:0] rd_a_phy;
logic [5:0] rd_a_phy_old;
logic [5:0] rs1_a_phy;
logic [5:0] rs2_a_phy;

logic [5:0] rd_b_phy;
logic [5:0] rd_b_phy_old;
logic [5:0] rs1_b_phy;
logic [5:0] rs2_b_phy;

logic [3:0] ALUCtrl_a;
logic [3:0] ALUCtrl_b;

// Instruction LUT
localparam i_type	= 7'b0010011;
localparam lw		= 7'b0000011;
localparam sw 		= 7'b0100011;

// Declare the register alias table
logic [5:0] rat [31:0];
logic [5:0] rat_ptr;

// Declare the free_pool table, implemented as a circular queue
logic [5:0] free_pool [63:0]; 
logic [5:0] free_pool_ptr_head;
logic [5:0] free_pool_ptr_tail;

logic [1:0] free_pool_ptr_incr; // Detects if we don't need to assign an rd register
assign free_pool_ptr_incr = {((opcode_a == sw) || (rd_a_arch == '0)), ((opcode_b == sw) || (rd_b_arch == '0))};

always_comb begin // Need to account for SW instructions which do not have an rd register!
	rs1_a_phy 	= rat[rs1_a_arch];
	
	if (opcode_a == i_type || opcode_a == lw) begin // No rs2;
		rs2_a_phy = '0;
	end else begin 
		rs2_a_phy = rat[rs2_a_arch];
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
			rd_a_phy		= '0;
			rd_a_phy_old 	= '0;
			rd_b_phy		= '0;
			rd_b_phy_old 	= '0;
		end
		2'b10: begin // A is a SW or x0, B has a valid rd
			rd_a_phy 		= '0;
			rd_a_phy_old 	= '0;
			rd_b_phy 		= free_pool[free_pool_ptr_head];
			rd_b_phy_old 	= rat[rd_b_arch];
		end
		2'b01: begin // B is a SW or x0, A has a valid rd
			rd_a_phy 		= free_pool[free_pool_ptr_head];
			rd_a_phy_old 	= rat[rd_a_arch];
			rd_b_phy			= '0;
			rd_b_phy_old 	= '0;
		end
		2'b00: begin // Neither A or B are SW or x0
			rd_a_phy 		= free_pool[free_pool_ptr_head];
			rd_a_phy_old 	= rat[rd_a_arch];
			rd_b_phy 		= free_pool[free_pool_ptr_head + 6'b1];
			rd_b_phy_old 	= rat[rd_b_arch];
		end
		default: begin
		    rd_a_phy		= '0;
			rd_a_phy_old 	= '0;
			rd_b_phy		= '0;
			rd_b_phy_old 	= '0;
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
				rat[rd_b_arch] 							<= free_pool[free_pool_ptr_head]; 
				free_pool[free_pool_ptr_head] 			<= '0;
				free_pool_ptr_head						<= free_pool_ptr_head + 6'd1;
			end
			2'b01: begin // B is a SW or x0, A has a valid rd
				rat[rd_a_arch] 							<= free_pool[free_pool_ptr_head]; 
				free_pool[free_pool_ptr_head] 			<= '0;
				free_pool_ptr_head						<= free_pool_ptr_head + 6'd1;
			end
			2'b00: begin // Both are SW
				rat[rd_a_arch]							<= free_pool[free_pool_ptr_head]; 
				rat[rd_b_arch]							<= free_pool[free_pool_ptr_head + 6'd1]; 				
				free_pool[free_pool_ptr_head] 			<= '0;
				free_pool[free_pool_ptr_head + 6'b1] 	<= '0;
				free_pool_ptr_head						<= free_pool_ptr_head + 6'd2;
			end
			default: begin
			end
		endcase
	end
end


// LUT for 4 bit operations
localparam ctrl_and = 4'b0000;
localparam ctrl_or 	= 4'b0001;
localparam ctrl_add = 4'b0010;
localparam ctrl_sub = 4'b0110;
localparam ctrl_xor = 4'b0011;
localparam ctrl_sra	= 4'b1110;

// LUT for ALU 2-bit control signals
localparam op_add   = 2'b00;
localparam op_sub   = 2'b01;
localparam op_rtype = 2'b10;
localparam op_itype = 2'b11;

// LUT for funct3
localparam f3_math = 3'b000; 
localparam f3_xor  = 3'b100;
localparam f3_sr   = 3'b101;
localparam f3_or   = 3'b110;
localparam f3_and  = 3'b111;

// LUT for funct7
localparam primary   = 7'b0000000; 
localparam secondary = 7'b0100000;

// Continue decoding ALUOp
always_comb begin // Decode ALU control signal for instr a
    unique case(ALUOp_a) 
        op_add: begin
            ALUCtrl_a = ctrl_add;
        end
        op_sub: begin
            ALUCtrl_a = ctrl_sub;
        end
        op_rtype: begin
            unique case(funct3_a) 
                f3_math: begin
                    if (funct7_a == primary) begin
                        ALUCtrl_a = ctrl_add;
                    end else begin
                        ALUCtrl_a = ctrl_sub;
                    end
                end
                f3_xor: begin
                    ALUCtrl_a = ctrl_xor;
                end
                f3_sr: begin
                    ALUCtrl_a = ctrl_sra;
                end
                f3_or: begin
                    ALUCtrl_a = ctrl_or;
                end
                f3_and: begin
                    ALUCtrl_a = ctrl_and;
                end
                default: begin
                    ALUCtrl_a = 4'b1111;
                end
            endcase
        end
        op_itype: begin
            unique case(funct3_a) 
                f3_math: begin
                    ALUCtrl_a = ctrl_add; // There is no subi instruction (Use addi with negative immediate)
                end
                f3_xor: begin
                    ALUCtrl_a = ctrl_xor;
                end
                f3_sr: begin
                    ALUCtrl_a = ctrl_sra;
                end
                f3_or: begin
                    ALUCtrl_a = ctrl_or;
                end
                f3_and: begin
                    ALUCtrl_a = ctrl_and;
                end
                default: begin
                    ALUCtrl_a = 4'b1111;
                end
            endcase
        end
        default: begin
            ALUCtrl_a = 4'b1111;
        end
    endcase
end

always_comb begin // Decode ALU control signal for instr b
    unique case(ALUOp_b) 
        op_add: begin
            ALUCtrl_b = ctrl_add;
        end
        op_sub: begin
            ALUCtrl_b = ctrl_sub;
        end
        op_rtype: begin
            unique case(funct3_b) 
                f3_math: begin
                    if (funct7_b == primary) begin
                        ALUCtrl_b = ctrl_add;
                    end else begin
                        ALUCtrl_b = ctrl_sub;
                    end
                end
                f3_xor: begin
                    ALUCtrl_b = ctrl_xor;
                end
                f3_sr: begin
                    ALUCtrl_b = ctrl_sra;
                end
                f3_or: begin
                    ALUCtrl_b = ctrl_or;
                end
                f3_and: begin
                    ALUCtrl_b = ctrl_and;
                end
                default: begin
                    ALUCtrl_b = 4'b1111;
                end
            endcase
        end
        op_itype: begin
            unique case(funct3_b) 
                f3_math: begin
                    ALUCtrl_b = ctrl_add; // There is no subi instruction (Use addi with negative immediate)
                end
                f3_xor: begin
                    ALUCtrl_b = ctrl_xor;
                end
                f3_sr: begin
                    ALUCtrl_b = ctrl_sra;
                end
                f3_or: begin
                    ALUCtrl_b = ctrl_or;
                end
                f3_and: begin
                    ALUCtrl_b = ctrl_and;
                end
                default: begin
                    ALUCtrl_b = 4'b1111;
                end
            endcase
        end
        default: begin
            ALUCtrl_b = 4'b1111;
        end
    endcase
end

always_ff @ (posedge clk) begin // Pass through, no physical register computation
    if (reset) begin // If in reset, push zeros
    	dispatch_reg_a.pc 		<= '0;
        dispatch_reg_a.opcode	<= '0;
        dispatch_reg_a.imm		<= '0;
        
        dispatch_reg_a.control.MemRead   <= '0;
        dispatch_reg_a.control.MemtoReg  <= '0;
        dispatch_reg_a.control.ALUOp     <= '0;
        dispatch_reg_a.control.MemWrite  <= '0;
        dispatch_reg_a.control.ALUSrc    <= '0;
        dispatch_reg_a.control.RegWrite  <= '0;
        
        dispatch_reg_b.pc 		<= '0;
        dispatch_reg_b.opcode	<= '0;
        dispatch_reg_b.imm		<= '0;
        
        dispatch_reg_b.control.MemRead   <= '0;
        dispatch_reg_b.control.MemtoReg  <= '0;
        dispatch_reg_b.control.ALUOp     <= '0;
        dispatch_reg_b.control.MemWrite  <= '0;
        dispatch_reg_b.control.ALUSrc    <= '0;
        dispatch_reg_b.control.RegWrite  <= '0;
        
    end else begin
        dispatch_reg_a.pc 		<= rename_reg_a.pc;
        dispatch_reg_a.opcode	<= rename_reg_a.opcode;
        dispatch_reg_a.imm		<= rename_reg_a.imm;
        dispatch_reg_a.control	<= rename_reg_a.control;
        
        dispatch_reg_b.pc 		<= rename_reg_b.pc;
        dispatch_reg_b.opcode	<= rename_reg_b.opcode;
        dispatch_reg_b.imm		<= rename_reg_b.imm;
        dispatch_reg_b.control	<= rename_reg_b.control;
	end
end

always_ff @ (posedge clk) begin	// Push new physical register addresses to pipeline registers
    if (reset) begin // If in reset, push zeros
        dispatch_reg_a.rd		<= '0;
        dispatch_reg_a.rd_old	<= '0;
        dispatch_reg_a.rs1		<= '0;
        dispatch_reg_a.rs2		<= '0;
        
        dispatch_reg_b.rd		<= '0;
        dispatch_reg_b.rd_old	<= '0;
        dispatch_reg_b.rs1		<= '0;
        dispatch_reg_b.rs2		<= '0;
        
        dispatch_reg_a.ALUCtrl  <= '0;
        dispatch_reg_b.ALUCtrl  <= '0;
    end else begin
        dispatch_reg_a.rd		<= rd_a_phy;
        dispatch_reg_a.rd_old	<= rd_a_phy_old;
        dispatch_reg_a.rs1		<= rs1_a_phy;
        dispatch_reg_a.rs2		<= rs2_a_phy;
        
        dispatch_reg_b.rd		<= rd_b_phy;
        dispatch_reg_b.rd_old	<= rd_b_phy_old;
        dispatch_reg_b.rs1		<= rs1_b_phy;
        dispatch_reg_b.rs2		<= rs2_b_phy;
        
        dispatch_reg_a.ALUCtrl  <= ALUCtrl_a;
        
        dispatch_reg_b.ALUCtrl  <= ALUCtrl_b;
	end
end

property valid_ALUCtrl_a; // Check that the ALU control signal decode (second stage) does not produce an invalid control signal because of garbage input
    @(posedge clk) disable iff (reset)
    (ALUCtrl_a != 4'b1111);
endproperty

assert property (valid_ALUCtrl_a);

property valid_ALUCtrl_b; // Check that the ALU control signal decode (second stage) does not produce an invalid control signal because of garbage input
    @(posedge clk) disable iff (reset)
    (ALUCtrl_b != 4'b1111);
endproperty

assert property (valid_ALUCtrl_b);

endmodule