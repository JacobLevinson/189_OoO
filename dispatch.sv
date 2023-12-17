`timescale 1ns/100ps

module dispatch import typedefs::*; (
input clk,
input reset,
input dispatchStruct dispatch_reg_a,
input dispatchStruct dispatch_reg_b,
output rsEntry rsLine_a,
output rsEntry rsLine_b,
output logic[63:0] phy_reg_rdy
// These are wired to the regfile
output regReqStruct reg_request [1:0], // Combinational

// These are wired from the regfile
input regRespStruct reg_response [1:0], // Combinational
// ROB register freeing/fowarding -> Must be a wire on the complete/ROB side
);

logic[3:0] rs_rob_ptr; // Assigns the RS and ROB positions
logic fu_assignment; // Used to equitably assign FUs
logic[1:0] fu_incr; // Flags used to increment the FU assignments

always_ff @(posedge clk) begin
    if (reset) begin
        rs_rob_ptr      <= '0;
        fu_assignment   <= '0;
        
        phy_reg_rdy     <= '1;
    end else begin
        if (dispatch_reg_a.opcode) begin // If opcode is valid
            rs_rob_ptr      <= rs_rob_ptr + 2; // Just going to assume that we'll never have to stall, add more entries to RS and ROB if we end up with issues
            fu_assignment   <= fu_assignment + fu_incr;
            
            if (!dispatch_reg_a.control.MemWrite) begin // If a is not SW, we can mark a register as "in use"
                phy_reg_rdy[dispatch_reg_a.rd] <= '0;
            end
            if (!dispatch_reg_b.control.MemWrite) begin // If b is not SW, we can mark a register as "in use"
                phy_reg_rdy[dispatch_reg_b.rd] <= '0;
            end
        end
    end
end

always_comb begin // Assign the FUs
    if (dispatch_reg_a.opcode) begin
        if (dispatch_reg_a.control.MemRead || dispatch_reg_a.control.MemWrite || dispatch_reg_a.control.MemtoReg) begin 
            // If the memory control signals indicate a memory operation
            rsLine_a.fu = 2'b10; // Memory FU
            if (dispatch_reg_b.control.MemRead || dispatch_reg_a.control.MemWrite || dispatch_reg_a.control.MemtoReg) begin
                // If the memory control signals indicate a memory operation
                rsLine_b.fu = 2'b10; // Memory FU
                fu_incr = 2'b00;
            end else begin 
                // Regular ALU operation
                rsLine_b.fu = fu_assignment;
                fu_incr = 2'b01;
            end
        end else begin
            rsLine_a.fu = fu_assignment; 
            // Regular ALU operation
            if (dispatch_reg_b.control.MemRead || dispatch_reg_a.control.MemWrite || dispatch_reg_a.control.MemtoReg) begin
                // If the memory control signals indicate a memory operation
                rsLine_b.fu = 2'b10; // Memory FU
                fu_incr = 2'b01;
            end else begin 
                // Regular ALU operation
                rsLine_b.fu = fu_assignment + 2'b1;
                fu_incr = 2'b10;
            end
        end
    end else begin
        fu_incr     = '0;
        rsLine_a.fu = '0;
        rsLine_b.fu = '0;
    end
end

always_comb begin
    if (dispatch_reg_a.opcode) begin
        rsLine_a.valid          = 1'b1;
        rsLine_a.instruction    = dispatch_reg_a;
        rsLine_a.src1rdy        = phy_reg_rdy[dispatch_reg_a.rs1]; // Will be updated further in RS table
        rsLine_a.src2rdy        = rsLine_a.instruction.control.ALUSrc ? 1'b1 : phy_reg_rdy[dispatch_reg_a.rs2]; // Will be updated further in RS table
        // This line checks that if we are to use an immediate, then ignore what is in the rs2 field for register readiness
        reg_request[0].RegWrite = '0;
        reg_request[0].rs1 = dispatch_reg_a.rs1;
        reg_request[0].rs2 = dispatch_reg_a.rs2;
        reg_request[0].rd  = dispatch_reg_a.rd;
        reg_request[0].wr_data = '0;
        rsLine_a.src1val        = reg_response[0].rs1_data;
        rsLine_a.src2val        = reg_response[0].rs2_data;
        rsLine_a.robNum         = rs_rob_ptr;
    end else begin
        rsLine_a.valid          = '0;
        rsLine_a.instruction.pc       = '0;
        rsLine_a.instruction.opcode   = '0;
        rsLine_a.instruction.rd       = '0;
        rsLine_a.instruction.rd_old   = '0;
        rsLine_a.instruction.rs1      = '0;
        rsLine_a.instruction.rs2      = '0;
        rsLine_a.instruction.imm      = '0;
        rsLine_a.instruction.ALUCtrl  = '0;
        rsLine_a.instruction.control.MemRead  = '0;
        rsLine_a.instruction.control.MemtoReg = '0;
        rsLine_a.instruction.control.ALUOp    = '0;
        rsLine_a.instruction.control.MemWrite = '0;
        rsLine_a.instruction.control.ALUSrc   = '0;
        rsLine_a.instruction.control.RegWrite = '0;   
        rsLine_a.src1rdy        = '0;
        rsLine_a.src2rdy        = '0;
        rsLine_a.robNum         = '0;

        //reg req
        reg_request[0].RegWrite = '0;
        reg_request[0].rs1 = '0;
        reg_request[0].rs2 = '0;
        reg_request[0].rd  = '0;
        reg_request[0].wr_data = '0;
        rsLine_a.src1val        = '0;
        rsLine_a.src2val        = '0;
    end
    if (dispatch_reg_b.opcode) begin
        rsLine_b.valid          = 1'b1;
        rsLine_b.instruction    = dispatch_reg_b;
        rsLine_b.src1rdy        = phy_reg_rdy[dispatch_reg_b.rs1]; // Will be updated further in RS table
        rsLine_b.src2rdy        = rsLine_b.instruction.control.ALUSrc ? 1'b1 : phy_reg_rdy[dispatch_reg_b.rs2]; // Will be updated further in RS table
        // This line checks that if we are to use an immediate, then ignore what is in the rs2 field for register readiness
        reg_request[1].RegWrite = '0;
        reg_request[1].rs1 = dispatch_reg_b.rs1;
        reg_request[1].rs2 = dispatch_reg_b.rs2;
        reg_request[1].rd  = dispatch_reg_b.rd;
        reg_request[1].wr_data = '0;
        rsLine_a.src1val        = reg_response[1].rs1_data;
        rsLine_a.src2val        = reg_response[1].rs2_data;

        rsLine_b.robNum         = rs_rob_ptr + 1'b1;
     end else begin
        rsLine_b.valid          = '0;
        rsLine_b.instruction.pc       = '0;
        rsLine_b.instruction.opcode   = '0;
        rsLine_b.instruction.rd       = '0;
        rsLine_b.instruction.rd_old   = '0;
        rsLine_b.instruction.rs1      = '0;
        rsLine_b.instruction.rs2      = '0;
        rsLine_b.instruction.imm      = '0;
        rsLine_b.instruction.ALUCtrl  = '0;
        rsLine_b.instruction.control.MemRead  = '0;
        rsLine_b.instruction.control.MemtoReg = '0;
        rsLine_b.instruction.control.ALUOp    = '0;
        rsLine_b.instruction.control.MemWrite = '0;
        rsLine_b.instruction.control.ALUSrc   = '0;
        rsLine_b.instruction.control.RegWrite = '0;  
        rsLine_b.src1rdy        = '0;
        rsLine_b.src2rdy        = '0;
        rsLine_b.robNum         = '0;

        //reg req
        reg_request[1].RegWrite = '0;
        reg_request[1].rs1 = '0;
        reg_request[1].rs2 = '0;
        reg_request[1].rd  = '0;
        reg_request[1].wr_data = '0;
        rsLine_b.src1val        = '0;
        rsLine_b.src2val        = '0;
    end
end
        
endmodule
