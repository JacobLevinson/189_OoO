`timescale 1ns/100ps

module complete_rob import typedefs::*;(
    input logic clk,
    input logic reset,
    input completeStruct complete0,
    input completeStruct complete1,
    input completeStruct complete2,
    input robDispatchStruct robDispatch_a,
    input robDispatchStruct robDispatch_b,
    output forwardingStruct forward_a,
    output forwardingStruct forward_b,
    output forwardingStruct forward_c,
    output robEntryStruct retire_instr_a, // Go to retire stage
    output robEntryStruct retire_instr_b  // Go to retire stage
);

// Declare ROB table
robEntryStruct rob_table [15:0];

always_comb begin // complete stage logic
    if (complete0.valid) begin
        forward_a.valid     = (complete0.control.MemRead || complete0.control.MemWrite) ? 1'b0 : 1'b1; // Exception for LW, LW will only forward from the mem stage
        forward_a.reg_addr  = complete0.rd;
        forward_a.data      = complete0.result;
    end else begin
        forward_a.valid     = '0;
        forward_a.reg_addr  = '0;
        forward_a.data      = '0;
    end
    if (complete1.valid) begin
        forward_b.valid     = (complete1.control.MemRead || complete1.control.MemWrite) ? 1'b0 : 1'b1;
        forward_b.reg_addr  = complete1.rd;
        forward_b.data      = complete1.result;
    end else begin
        forward_b.valid     = '0;
        forward_b.reg_addr  = '0;
        forward_b.data      = '0;
    end
    if (complete2.valid) begin
        forward_c.valid     = (complete2.control.MemRead || complete2.control.MemWrite) ? 1'b0 : 1'b1; // Exception for LW, LW will only forward from the mem stage
        forward_c.reg_addr  = complete2.rd;
        forward_c.data      = complete2.result;
    end else begin
        forward_c.valid     = '0;
        forward_c.reg_addr  = '0;
        forward_c.data      = '0;
    end
end

logic [3:0] rob_ptr;

integer i;
integer j;
always_ff @ (posedge clk) begin
    if(reset) begin // Initialize the ROB
        for (i = 0; i < 16; i = i + 1) begin 
            rob_table[i].valid      <= 0;
            rob_table[i].complete   <= 0;
            rob_table[i].pc         <= 0;
            rob_table[i].rd         <= 0;
            rob_table[i].rd_old     <= 0;
            rob_table[i].result     <= 0;
            rob_table[i].wr_data    <= 0;
            rob_table[i].control.MemRead  <= '0;
            rob_table[i].control.MemtoReg <= '0;
            rob_table[i].control.ALUOp    <= '0;
            rob_table[i].control.MemWrite <= '0;
            rob_table[i].control.ALUSrc   <= '0;
            rob_table[i].control.RegWrite <= '0;   
        end
        rob_ptr <= '0;
    end else begin
        for (j = 0; j < 16; j = j + 1) begin
            if (robDispatch_a.robNum == j) begin
                if (robDispatch_a.valid) begin
                    rob_table[robDispatch_a.robNum].valid       <= robDispatch_a.valid;
                    rob_table[robDispatch_a.robNum].pc          <= robDispatch_a.pc;
                    rob_table[robDispatch_a.robNum].rd          <= robDispatch_a.rd;
                    rob_table[robDispatch_a.robNum].rd_old      <= robDispatch_a.rd_old;
                    rob_table[robDispatch_a.robNum].control     <= robDispatch_a.control;
                    // Other entries in the ROB table stay initialized to zero until completion
                end
            end else if (robDispatch_b.robNum == j) begin
                if (robDispatch_b.valid) begin
                    rob_table[robDispatch_b.robNum].valid       <= robDispatch_b.valid; 
                    rob_table[robDispatch_b.robNum].pc          <= robDispatch_b.pc;
                    rob_table[robDispatch_b.robNum].rd          <= robDispatch_b.rd;
                    rob_table[robDispatch_b.robNum].rd_old      <= robDispatch_b.rd_old;
                    rob_table[robDispatch_b.robNum].control     <= robDispatch_b.control;
                    // Other entries in the ROB table stay initialized to zero until completion
                end
            end 
            
            if (complete0.robNum == j) begin       
                if (complete0.valid) begin
                    rob_table[complete0.robNum].complete    <= '1;
                    rob_table[complete0.robNum].result      <= complete0.result;
                    rob_table[complete0.robNum].wr_data     <= complete0.wr_data;
                end
           end else if (complete1.robNum == j) begin
                if (complete1.valid) begin
                    rob_table[complete1.robNum].complete    <= '1;
                    rob_table[complete1.robNum].result      <= complete1.result;
                    rob_table[complete1.robNum].wr_data     <= complete1.wr_data;
                end
           end else if (complete2.robNum == j) begin
                if (complete2.valid) begin
                    rob_table[complete2.robNum].complete    <= '1;
                    rob_table[complete2.robNum].result      <= complete2.result;
                    rob_table[complete2.robNum].wr_data     <= complete2.wr_data; 
                end
           end
           
           if (rob_ptr == j) begin // retire signals - just send the to entries out if they are ready
                if (rob_table[rob_ptr].complete && rob_table[rob_ptr].valid) begin
                    retire_instr_a              <= rob_table[rob_ptr];
                    
                    rob_table[rob_ptr].valid    <= 0;
                    rob_table[rob_ptr].complete <= 0;
                    rob_table[rob_ptr].pc       <= 0;
                    rob_table[rob_ptr].rd       <= 0;
                    rob_table[rob_ptr].rd_old   <= 0;
                    rob_table[rob_ptr].result   <= 0;
                    rob_table[rob_ptr].wr_data  <= 0;
                    rob_table[rob_ptr].control.MemRead  <= '0;
                    rob_table[rob_ptr].control.MemtoReg <= '0;
                    rob_table[rob_ptr].control.ALUOp    <= '0;
                    rob_table[rob_ptr].control.MemWrite <= '0;
                    rob_table[rob_ptr].control.ALUSrc   <= '0;
                    rob_table[rob_ptr].control.RegWrite <= '0;  
                    if (rob_table[rob_ptr + 1'b1].complete && rob_table[rob_ptr + 1'b1].valid) begin
                        retire_instr_b              <= rob_table[rob_ptr + 1'b1];
                    
                        rob_table[rob_ptr + 1'b1].valid     <= 0;
                        rob_table[rob_ptr + 1'b1].complete  <= 0;
                        rob_table[rob_ptr + 1'b1].pc        <= 0;
                        rob_table[rob_ptr + 1'b1].rd        <= 0;
                        rob_table[rob_ptr + 1'b1].rd_old    <= 0;
                        rob_table[rob_ptr + 1'b1].result    <= 0;
                        rob_table[rob_ptr + 1'b1].wr_data   <= 0;
                        rob_table[rob_ptr + 1'b1].control.MemRead   <= '0;
                        rob_table[rob_ptr + 1'b1].control.MemtoReg  <= '0;
                        rob_table[rob_ptr + 1'b1].control.ALUOp     <= '0;
                        rob_table[rob_ptr + 1'b1].control.MemWrite  <= '0;
                        rob_table[rob_ptr + 1'b1].control.ALUSrc    <= '0;
                        rob_table[rob_ptr + 1'b1].control.RegWrite  <= '0;  
                        
                        rob_ptr <= rob_ptr + 2'b10;
                    end else begin
                        retire_instr_b.valid <= '0;
                        rob_ptr <= rob_ptr + 1'b1;
                    end
                end else begin
                    retire_instr_a.valid <= '0;
                    retire_instr_b.valid <= '0;
                end
            end  
        end
    end
end

endmodule