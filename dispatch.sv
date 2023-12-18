`timescale 1ns/100ps

module dispatch import typedefs::*; (
input clk,
input reset,
input dispatchStruct dispatch_reg_a,
input dispatchStruct dispatch_reg_b,

input forwardingStruct forward_a,
input forwardingStruct forward_b,
input forwardingStruct forward_c,
input forwardingStruct forward_d,
input forwardingStruct forward_e,

// These are wired to the regfile
output regReqStruct reg_request_a, // Combinational
output regReqStruct reg_request_b,
// These are wired from the regfile
input regRespStruct reg_response_a, // Combinational
input regRespStruct reg_response_b,

output rsEntry rsLine_a, // Output to RS
output rsEntry rsLine_b,
output robDispatchStruct robDispatch_a, // Output to ROB
output robDispatchStruct robDispatch_b
);

logic[3:0] rs_rob_ptr; // Assigns the RS and ROB positions
logic fu_assignment; // Used to equitably assign FUs
logic[1:0] fu_incr; // Flags used to increment the FU assignments

logic[63:0] phy_reg_rdy;
logic[31:0] forwarded_regs [63:0];
logic[63:0] forward_valid;

integer i;
always_ff @(posedge clk) begin
    if (reset) begin
        rs_rob_ptr      <= '0;
        fu_assignment   <= '0;
        phy_reg_rdy     <= '1;
        
        for (i = 0; i < 64; i = i + 1) begin
            forwarded_regs[i] = '1;
        end
        forward_valid <= '0;
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
        
        if (forward_a.valid) begin
            phy_reg_rdy[forward_a.reg_addr]      <= '1;
            forwarded_regs[forward_a.reg_addr]   <= forward_a.data;
            forward_valid[forward_a.reg_addr]    <= '1;
        end
        
        if (forward_b.valid) begin
            phy_reg_rdy[forward_b.reg_addr]      <= '1;
            forwarded_regs[forward_b.reg_addr]   <= forward_b.data;
            forward_valid[forward_b.reg_addr]    <= '1;
        end
        
        if (forward_c.valid) begin
            phy_reg_rdy[forward_c.reg_addr]      <= '1;
            forwarded_regs[forward_c.reg_addr]   <= forward_c.data;
            forward_valid[forward_c.reg_addr]    <= '1;
        end
        
        if (forward_d.valid) begin
            phy_reg_rdy[forward_d.reg_addr]      <= '1;
            forwarded_regs[forward_d.reg_addr]   <= forward_d.data;
            forward_valid[forward_d.reg_addr]    <= '1;
        end
        
        if (forward_e.valid) begin
            phy_reg_rdy[forward_e.reg_addr]      <= '1;
            forwarded_regs[forward_e.reg_addr]   <= forward_e.data;
            forward_valid[forward_e.reg_addr]    <= '1;
        end
    end
end

always_comb begin // Assign the FUs
    if (dispatch_reg_a.opcode) begin
        if (dispatch_reg_a.control.MemRead || dispatch_reg_a.control.MemtoReg) begin 
            // If the memory control signals indicate a memory read operation (stores only take 1 cycle)
            rsLine_a.fu = 2'b10; // Memory FU
            if (dispatch_reg_b.control.MemRead || dispatch_reg_a.control.MemtoReg) begin
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
            if (dispatch_reg_b.control.MemRead || dispatch_reg_a.control.MemtoReg) begin
                // If the memory control signals indicate a memory operation (stores only take 1 cycle)
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

always_comb begin // Read requests to registers
    if (dispatch_reg_a.opcode) begin
        reg_request_a.RegWrite  = '0; // Read only
        reg_request_a.rs1       = dispatch_reg_a.rs1;
        reg_request_a.rs2       = dispatch_reg_a.rs2;
        reg_request_a.rd        = dispatch_reg_a.rd;
        reg_request_a.wr_data   = '0;
    end else begin // No instruction
        reg_request_a.RegWrite  = '0;
        reg_request_a.rs1       = '0;
        reg_request_a.rs2       = '0;
        reg_request_a.rd        = '0;
        reg_request_a.wr_data   = '0;
    end
    
    if (dispatch_reg_b.opcode) begin
        reg_request_b.RegWrite  = '0; // Read only
        reg_request_b.rs1       = dispatch_reg_b.rs1;
        reg_request_b.rs2       = dispatch_reg_b.rs2;
        reg_request_b.rd        = dispatch_reg_b.rd;
        reg_request_b.wr_data   = '0;
    end else begin // No instruction
        reg_request_b.RegWrite  = '0;
        reg_request_b.rs1       = '0;
        reg_request_b.rs2       = '0;
        reg_request_b.rd        = '0;
        reg_request_b.wr_data   = '0;
    end
end

always_comb begin // Wire to reservation station
    if (dispatch_reg_a.opcode) begin
        rsLine_a.valid          = 1'b1;
        rsLine_a.instruction    = dispatch_reg_a;
        
        if (dispatch_reg_a.rs1 == '0) begin
            rsLine_a.rs1_rdy    = '1;
            rsLine_a.rs1_data   = '0;
        end else if (forward_valid[dispatch_reg_a.rs1]) begin
            rsLine_a.rs1_rdy    = phy_reg_rdy[dispatch_reg_a.rs1];
            rsLine_a.rs1_data   = forwarded_regs[dispatch_reg_a.rs1];
        end else if (forward_a.valid && dispatch_reg_a.rs1 == forward_a.reg_addr) begin
            rsLine_a.rs1_rdy    = '1;
            rsLine_a.rs1_data   = forward_a.data;
        end else if (forward_b.valid && dispatch_reg_a.rs1 == forward_b.reg_addr) begin
            rsLine_a.rs1_rdy    = '1;
            rsLine_a.rs1_data   = forward_b.data;
        end else if (forward_c.valid && dispatch_reg_a.rs1 == forward_c.reg_addr) begin
            rsLine_a.rs1_rdy    = '1;
            rsLine_a.rs1_data   = forward_c.data;
        end else if (forward_d.valid && dispatch_reg_a.rs1 == forward_d.reg_addr) begin
            rsLine_a.rs1_rdy    = '1;
            rsLine_a.rs1_data   = forward_d.data;
        end else if (forward_e.valid && dispatch_reg_a.rs1 == forward_e.reg_addr) begin
            rsLine_a.rs1_rdy    = '1;
            rsLine_a.rs1_data   = forward_e.data;
        end else begin     
            rsLine_a.rs1_rdy    = phy_reg_rdy[dispatch_reg_a.rs1];
            rsLine_a.rs1_data   = reg_response_a.rs1_data;
        end
        
        if (dispatch_reg_a.rs2 == '0) begin
            rsLine_a.rs2_rdy    = '1;
            rsLine_a.rs2_data   = '0;
        end else if (forward_valid[dispatch_reg_a.rs2]) begin
            rsLine_a.rs2_rdy    = rsLine_a.instruction.control.ALUSrc ? 1'b1 : phy_reg_rdy[dispatch_reg_a.rs2];
            rsLine_a.rs2_data   = forwarded_regs[dispatch_reg_a.rs2];
        end else if (forward_a.valid && dispatch_reg_a.rs2 == forward_a.reg_addr) begin
            rsLine_a.rs2_rdy    = '1;
            rsLine_a.rs2_data   = forward_a.data;
        end else if (forward_b.valid && dispatch_reg_a.rs2 == forward_b.reg_addr) begin
            rsLine_a.rs2_rdy    = '1;
            rsLine_a.rs2_data   = forward_b.data;
        end else if (forward_c.valid && dispatch_reg_a.rs2 == forward_c.reg_addr) begin
            rsLine_a.rs2_rdy    = '1;
            rsLine_a.rs2_data   = forward_c.data;
        end else if (forward_d.valid && dispatch_reg_a.rs2 == forward_d.reg_addr) begin
            rsLine_a.rs2_rdy    = '1;
            rsLine_a.rs2_data   = forward_d.data;
        end else if (forward_e.valid && dispatch_reg_a.rs2 == forward_e.reg_addr) begin
            rsLine_a.rs2_rdy    = '1;
            rsLine_a.rs2_data   = forward_e.data;
        end else begin     
            rsLine_a.rs2_rdy    = (dispatch_reg_a.control.ALUSrc && !dispatch_reg_a.control.MemWrite) ? 1'b1 : phy_reg_rdy[dispatch_reg_a.rs2];
            rsLine_a.rs2_data   = reg_response_a.rs1_data;
        end
        
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
        rsLine_a.rs1_rdy        = '0;
        rsLine_a.rs2_rdy        = '0;        
        rsLine_a.rs1_data       = '0;
        rsLine_a.rs2_data       = '0;
        rsLine_a.robNum         = '0;
    end
    
    if (dispatch_reg_b.opcode) begin
        rsLine_b.valid          = 1'b1;
        rsLine_b.instruction    = dispatch_reg_b;
        
        if (dispatch_reg_b.rs1 == '0) begin
            rsLine_b.rs1_rdy    = '1;
            rsLine_b.rs1_data   = '0;
        end else if (forward_valid[dispatch_reg_b.rs1]) begin // If stored in the forwarding buffer
            rsLine_b.rs1_rdy    = (dispatch_reg_b.rs1 != dispatch_reg_a.rd) ? phy_reg_rdy[dispatch_reg_b.rs1] : '0;
            rsLine_b.rs1_data   = forwarded_regs[dispatch_reg_b.rs1];
        end else if (forward_a.valid && dispatch_reg_b.rs1 == forward_a.reg_addr) begin // Just forwarded this cycle
            rsLine_b.rs1_rdy    = '1;
            rsLine_b.rs1_data   = forward_a.data;
        end else if (forward_b.valid && dispatch_reg_b.rs1 == forward_b.reg_addr) begin
            rsLine_b.rs1_rdy    = '1;
            rsLine_b.rs1_data   = forward_b.data;
        end else if (forward_c.valid && dispatch_reg_b.rs1 == forward_c.reg_addr) begin
            rsLine_b.rs1_rdy    = '1;
            rsLine_b.rs1_data   = forward_c.data;
        end else if (forward_d.valid && dispatch_reg_b.rs1 == forward_d.reg_addr) begin
            rsLine_b.rs1_rdy    = '1;
            rsLine_b.rs1_data   = forward_d.data;
        end else if (forward_e.valid && dispatch_reg_b.rs1 == forward_e.reg_addr) begin
            rsLine_b.rs1_rdy    = '1;
            rsLine_b.rs1_data   = forward_e.data;        
        end else begin     
            rsLine_b.rs1_rdy    = (dispatch_reg_b.rs1 != dispatch_reg_a.rd) ? phy_reg_rdy[dispatch_reg_b.rs1] : '0;
            rsLine_b.rs1_data   = reg_response_b.rs1_data;
        end
        
        if (dispatch_reg_b.rs2 == '0) begin
            rsLine_b.rs2_rdy    = '1;
            rsLine_b.rs2_data   = '0;
        end else if (forward_valid[dispatch_reg_b.rs2]) begin // If stored in the forwarding buffer
            rsLine_b.rs2_rdy    = rsLine_b.instruction.control.ALUSrc ? 1'b1 : (dispatch_reg_b.rs2 != dispatch_reg_a.rd) ? phy_reg_rdy[dispatch_reg_b.rs2] : '0;
            rsLine_b.rs2_data   = forwarded_regs[dispatch_reg_b.rs2];
        end else if (forward_a.valid && dispatch_reg_b.rs2 == forward_a.reg_addr) begin // Just forwarded this cycle
            rsLine_b.rs2_rdy    = '1;
            rsLine_b.rs2_data   = forward_a.data;
        end else if (forward_b.valid && dispatch_reg_b.rs2 == forward_b.reg_addr) begin
            rsLine_b.rs2_rdy    = '1;
            rsLine_b.rs2_data   = forward_b.data;
        end else if (forward_c.valid && dispatch_reg_b.rs2 == forward_c.reg_addr) begin
            rsLine_b.rs2_rdy    = '1;
            rsLine_b.rs2_data   = forward_c.data;
        end else if (forward_d.valid && dispatch_reg_b.rs2 == forward_d.reg_addr) begin
            rsLine_b.rs2_rdy    = '1;
            rsLine_b.rs2_data   = forward_d.data;
        end else if (forward_e.valid && dispatch_reg_b.rs2 == forward_e.reg_addr) begin
            rsLine_b.rs2_rdy    = '1;
            rsLine_b.rs2_data   = forward_e.data;                        
        end else begin     
            rsLine_b.rs2_rdy    = (dispatch_reg_b.control.ALUSrc  && !dispatch_reg_b.control.MemWrite) ? 1'b1 : (dispatch_reg_b.rs2 != dispatch_reg_a.rd) ? phy_reg_rdy[dispatch_reg_b.rs2] : '0;
            rsLine_b.rs2_data   = reg_response_b.rs1_data;
        end
        
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
        rsLine_b.rs1_rdy        = '0;
        rsLine_b.rs2_rdy        = '0;
        rsLine_b.rs1_data       = '0;
        rsLine_b.rs2_data       = '0;
        rsLine_b.robNum         = '0;
    end
end

always_comb begin // Wire to reorder buffer
    if (dispatch_reg_a.opcode) begin
        robDispatch_a.valid     = '1;
        robDispatch_a.pc        = dispatch_reg_a.pc;
        robDispatch_a.rd        = dispatch_reg_a.rd;
        robDispatch_a.rd_old    = dispatch_reg_a.rd_old;
        robDispatch_a.robNum    = rs_rob_ptr;
        robDispatch_a.control   = dispatch_reg_a.control;
    end else begin
        robDispatch_a.pc        = '0;
        robDispatch_a.valid     = '0;
        robDispatch_a.rd        = '0;
        robDispatch_a.rd_old    = '0;
        robDispatch_a.robNum    = '0;
        robDispatch_a.control.MemRead   = '0;
        robDispatch_a.control.MemtoReg  = '0;
        robDispatch_a.control.ALUOp     = '0;
        robDispatch_a.control.MemWrite  = '0;
        robDispatch_a.control.ALUSrc    = '0;
        robDispatch_a.control.RegWrite  = '0;
    end
    
    if (dispatch_reg_b.opcode) begin
        robDispatch_b.valid     = '1;
        robDispatch_b.pc        = dispatch_reg_b.pc;
        robDispatch_b.rd        = dispatch_reg_b.rd;
        robDispatch_b.rd_old    = dispatch_reg_b.rd_old;
        robDispatch_b.robNum    = rs_rob_ptr + 1'b1;
        robDispatch_b.control   = dispatch_reg_b.control;
    end else begin
        robDispatch_b.pc        = '0;
        robDispatch_b.valid     = '0;
        robDispatch_b.rd        = '0;
        robDispatch_b.rd_old    = '0;
        robDispatch_b.robNum    = '0;
        robDispatch_b.control.MemRead   = '0;
        robDispatch_b.control.MemtoReg  = '0;
        robDispatch_b.control.ALUOp     = '0;
        robDispatch_b.control.MemWrite  = '0;
        robDispatch_b.control.ALUSrc    = '0;
        robDispatch_b.control.RegWrite  = '0;
    end    
end

property rd_zero_for_lw_a; // Ensures that if we have a SW instruction, the rd register fields are zeroed
    @(posedge clk) disable iff (!dispatch_reg_a.control.MemWrite)
    (dispatch_reg_a.rd == '0 && dispatch_reg_a.rd_old == '0);
endproperty

assert property(rd_zero_for_lw_a);

property rd_zero_for_lw_b; // Ensures that if we have a SW instruction, the rd register fields are zeroed
    @(posedge clk) disable iff (!dispatch_reg_b.control.MemWrite)
    (dispatch_reg_b.rd == '0 && dispatch_reg_b.rd_old == '0);
endproperty

assert property(rd_zero_for_lw_b);

endmodule