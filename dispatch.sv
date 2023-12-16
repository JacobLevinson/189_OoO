`timescale 1ns/100ps

module dispatch import typedefs::*; (
input clk,
input reset,
input dispatchStruct dispatch_reg_a,
input dispatchStruct dispatch_reg_b,
output rsEntry rsLine_a,
output rsEntry rsLine_b,
output logic[63:0] phy_reg_rdy
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
        rsLine_a.robNum         = rs_rob_ptr;
    
        rsLine_b.valid          = 1'b1;
        rsLine_b.instruction    = dispatch_reg_b;
        rsLine_b.src1rdy        = phy_reg_rdy[dispatch_reg_b.rs1]; // Will be updated further in RS table
        rsLine_b.src2rdy        = rsLine_b.instruction.control.ALUSrc ? 1'b1 : phy_reg_rdy[dispatch_reg_b.rs2]; // Will be updated further in RS table
        // This line checks that if we are to use an immediate, then ignore what is in the rs2 field for register readiness
        rsLine_b.robNum         = rs_rob_ptr;
     end else begin
        rsLine_a.valid          = '0;
        rsLine_a.instruction    = '0;
        rsLine_a.src1rdy        = '0;
        rsLine_a.src2rdy        = '0;
        rsLine_a.robNum         = '0;
    
        rsLine_b.valid          = '0;
        rsLine_b.instruction    = '0;
        rsLine_b.src1rdy        = '0;
        rsLine_b.src2rdy        = '0;
        rsLine_b.robNum         = '0;
    end
end
        
endmodule
