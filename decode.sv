`timescale 1ns/100ps

module decode import typedefs::*; (
input logic clk,
input fetchStruct fd_reg,
input reset,
output instStruct rename_reg_a,
output instStruct rename_reg_b
);

// Main instruction signals
logic [6:0] opcode_a;
logic [4:0] rd_a;
logic [4:0] rs1_a;
logic [4:0] rs2_a;
logic [2:0] funct3_a;
logic [6:0] funct7_a;
logic [31:0] imm_a;
logic [31:0] pc_a;

logic [6:0] opcode_b;
logic [4:0] rd_b;
logic [4:0] rs1_b;
logic [4:0] rs2_b;
logic [2:0] funct3_b;
logic [6:0] funct7_b;
logic [31:0] imm_b;
logic [31:0] pc_b;

always_comb begin // Parse instructions
	opcode_a = fd_reg.inst_a [6:0];
	rd_a	 = fd_reg.inst_a [11:7];
	funct3_a = fd_reg.inst_a [14:12];
	rs1_a    = fd_reg.inst_a [19:15];
	rs2_a    = fd_reg.inst_a [24:20];
	funct7_a = fd_reg.inst_a [31:25];
	
	opcode_b = fd_reg.inst_b [6:0];
	rd_b 	 = fd_reg.inst_b [11:7];
	funct3_b = fd_reg.inst_b [14:12];
	rs1_b    = fd_reg.inst_b [19:15];
	rs2_b    = fd_reg.inst_b [24:20];
	funct7_b = fd_reg.inst_b [31:25];
	
	pc_a 	 = fd_reg.pc_a; // These are simply passed through
	pc_b 	 = fd_reg.pc_b;
end

// LUT for ImmGen and Control Signals
localparam i_type   = 7'b0010011;
localparam load     = 7'b0000011;
localparam s_type	= 7'b0100011;
localparam r_type   = 7'b0110011;

always_comb begin // ImmGen for inst_a
	case (fd_reg.inst_a [6:0]) 
		i_type: begin 
			imm_a[11:0]		= fd_reg.inst_a[31:20];
			imm_a[31:12] 	= 'b0;
		end
		load: begin 
			imm_a[11:0]  	= fd_reg.inst_a[31:20];
			imm_a[31:12] 	= 'b0;
		end
		s_type: begin
			imm_a[4:0]   	= fd_reg.inst_a[11:7];
			imm_a[11:5]  	= fd_reg.inst_a[31:25];
			imm_a[31:12] 	= 'b0;
		end
		default:
			imm_a[31:0] 	= 'b0;
	endcase
end
	
always_comb begin // ImmGen for inst_b
	case (fd_reg.inst_b [6:0]) 
		i_type:  begin
			imm_b[11:0]  	= fd_reg.inst_b[31:20];
			imm_b[31:12] 	= 'b0;
		end
		load: begin
			imm_b[11:0]  	= fd_reg.inst_b[31:20];
			imm_b[31:12] 	= 'b0;
		end
		s_type: begin
			imm_b[4:0]   	= fd_reg.inst_b[11:7];
			imm_b[11:5]  	= fd_reg.inst_b[31:25];
			imm_b[31:12] 	= 'b0;
		end
		default:
			imm_b[31:0] 	= 'b0;
	endcase
end

// Control Signals
logic MemRead_a;
logic MemtoReg_a;
logic [1:0] ALUOp_a;
logic MemWrite_a;
logic ALUSrc_a;
logic RegWrite_a;

logic MemRead_b;
logic MemtoReg_b;
logic [1:0] ALUOp_b;
logic MemWrite_b;
logic ALUSrc_b;
logic RegWrite_b;

// LUT for ALU 2-bit control signals
localparam op_add   = 2'b00;
localparam op_sub   = 2'b01;
localparam op_rtype = 2'b10;
localparam op_itype = 2'b11;

always_comb begin // Generate control signals for a
	case (fd_reg.inst_a [6:0]) 
		r_type: begin 
			MemRead_a 	= 0;
			MemtoReg_a 	= 0;
			ALUOp_a    	= op_rtype;
			MemWrite_a 	= 0;
			ALUSrc_a   	= 0;
			RegWrite_a 	= 1;
		end
		i_type: begin 
			MemRead_a  	= 0;
			MemtoReg_a 	= 0;
			ALUOp_a    	= op_itype;
			MemWrite_a 	= 0;
			ALUSrc_a   	= 1;
			RegWrite_a 	= 1;
		end
		load: begin 
			MemRead_a  	= 1;
			MemtoReg_a 	= 1;
			ALUOp_a    	= op_add;
			MemWrite_a 	= 0;
			ALUSrc_a   	= 1;
			RegWrite_a 	= 1;
		end
		s_type: begin 
			MemRead_a  	= 0;
			MemtoReg_a 	= 0;
			ALUOp_a    	= op_add;
			MemWrite_a 	= 1;
			ALUSrc_a   	= 1;
			RegWrite_a 	= 0;
		end
		default: begin
			MemRead_a  	= 0;
			MemtoReg_a 	= 0;
			ALUOp_a    	= 2'b00;
			MemWrite_a 	= 0;
			ALUSrc_a   	= 0;
			RegWrite_a 	= 0;
		end
	endcase
end
		
always_comb begin // Generate control signals for b
	case (fd_reg.inst_b [6:0]) 
		r_type: begin 
			MemRead_b   = 0;
			MemtoReg_b  = 0;
			ALUOp_b		= op_rtype;
			MemWrite_b	= 0;
			ALUSrc_b	= 0;
			RegWrite_b	= 1;
		end
		i_type: begin 
			MemRead_b	= 0;
			MemtoReg_b	= 0;
			ALUOp_b	    = op_itype;
			MemWrite_b	= 0;
			ALUSrc_b	= 1;
			RegWrite_b	= 1;
		end
		load: begin
			MemRead_b	= 1;
			MemtoReg_b	= 1;
			ALUOp_b		= op_add;
			MemWrite_b	= 0;
			ALUSrc_b	= 1;
			RegWrite_b	= 1;
		end
		s_type: begin 
			MemRead_b	= 0;
			MemtoReg_b	= 0;
			ALUOp_b		= op_add;
			MemWrite_b	= 1;
			ALUSrc_b	= 1;
			RegWrite_b	= 0;
		end
		default: begin
			MemRead_b	= 0;
			MemtoReg_b	= 0;
			ALUOp_b		= 2'b00;
			MemWrite_b	= 0;
			ALUSrc_b	= 0;
			RegWrite_b	= 0;
		end
	endcase
end

always_ff @(posedge clk) begin // Push instruction a to pipeline registers
    if (reset) begin
        rename_reg_a.opcode    <= '0;
        rename_reg_a.rd        <= '0;
        rename_reg_a.funct3    <= '0;
        rename_reg_a.rs1       <= '0;
        rename_reg_a.rs2       <= '0;
        rename_reg_a.funct7    <= '0;
        
        rename_reg_a.imm       <= '0;
        rename_reg_a.pc        <= '0;
        
        rename_reg_a.control.MemRead   <= '0;
        rename_reg_a.control.MemtoReg  <= '0;
        rename_reg_a.control.ALUOp     <= '0;
        rename_reg_a.control.MemWrite  <= '0;
        rename_reg_a.control.ALUSrc    <= '0;
        rename_reg_a.control.RegWrite  <= '0;
    end else begin 
        rename_reg_a.opcode    <= opcode_a;
        rename_reg_a.rd        <= rd_a;
        rename_reg_a.funct3    <= funct3_a;
        rename_reg_a.rs1       <= rs1_a;
        rename_reg_a.rs2       <= rs2_a;
        rename_reg_a.funct7    <= funct7_a;
        
        rename_reg_a.imm       <= imm_a;
        rename_reg_a.pc        <= pc_a;
        
        rename_reg_a.control.MemRead   <= MemRead_a;
        rename_reg_a.control.MemtoReg  <= MemtoReg_a;
        rename_reg_a.control.ALUOp     <= ALUOp_a;
        rename_reg_a.control.MemWrite  <= MemWrite_a;
        rename_reg_a.control.ALUSrc    <= ALUSrc_a;
        rename_reg_a.control.RegWrite  <= RegWrite_a;
    end
end

always_ff @(posedge clk) begin // Push instruction b to pipeline registers
    if (reset) begin
        rename_reg_b.opcode    <= '0;
        rename_reg_b.rd        <= '0;
        rename_reg_b.funct3    <= '0;
        rename_reg_b.rs1       <= '0;
        rename_reg_b.rs2       <= '0;
        rename_reg_b.funct7    <= '0;
        
        rename_reg_b.imm       <= '0;
        rename_reg_b.pc        <= '0;
        
        rename_reg_b.control.MemRead   <= '0;
        rename_reg_b.control.MemtoReg  <= '0;
        rename_reg_b.control.ALUOp     <= '0;
        rename_reg_b.control.MemWrite  <= '0;
        rename_reg_b.control.ALUSrc    <= '0;
        rename_reg_b.control.RegWrite  <= '0;
    end else begin
        rename_reg_b.opcode    <= opcode_b;
        rename_reg_b.rd        <= rd_b;
        rename_reg_b.funct3    <= funct3_b;
        rename_reg_b.rs1       <= rs1_b;
        rename_reg_b.rs2       <= rs2_b;
        rename_reg_b.funct7    <= funct7_b;
        
        rename_reg_b.imm       <= imm_b;
        rename_reg_b.pc        <= pc_b;
        
        rename_reg_b.control.MemRead   <= MemRead_b;
        rename_reg_b.control.MemtoReg  <= MemtoReg_b;
        rename_reg_b.control.ALUOp     <= ALUOp_b;
        rename_reg_b.control.MemWrite  <= MemWrite_b;
        rename_reg_b.control.ALUSrc    <= ALUSrc_b;
        rename_reg_b.control.RegWrite  <= RegWrite_b;
    end
end

property valid_ctrl_signals_a; // Ensures that the control signals generated aren't held at zero because the opcode was garbage
    @(posedge clk) disable iff (reset)
    (MemRead_a || MemtoReg_a || (ALUOp_a == 2'b0) || MemWrite_a || ALUSrc_a || RegWrite_a);
endproperty

assert property(valid_ctrl_signals_a);

property valid_ctrl_signals_b; // Ensures that the control signals generated aren't held at zero because the opcode was garbage
    @(posedge clk) disable iff (reset)
    (MemRead_b || MemtoReg_b || (ALUOp_b == 2'b0) || MemWrite_b || ALUSrc_b || RegWrite_b);
endproperty

assert property(valid_ctrl_signals_b);

endmodule