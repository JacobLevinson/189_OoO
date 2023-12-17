`timescale 1ns/100ps

module complete_rob import typedefs::*;(
    input logic clk,
    input logic reset,
    input completeStruct complete1,
    input completeStruct complete2,
    input completeStruct complete3,
    input robDispatchStruct dispatch,
    output forwardStruct forwarding,
    output robEntryStruct rob_entry1, // Go to retire stage
    output robEntryStruct rob_entry2
);

robEntryStruct rob_table [15:0];

always_comb begin // complete stage logic
    if (complete1.valid) begin
        forwarding.valid1 = 1;
        forwarding.reg1 = complete1.rd;
        forwarding.val1 = complete1.result;
    end else begin
        forwarding.valid1 = 0;
        forwarding.reg1 = 0;
        forwarding.val1 = 0;
    end
    if (complete2.valid) begin
        forwarding.valid2 = 1;
        forwarding.reg2 = complete2.rd;
        forwarding.val2 = complete2.result;
    end else begin
        forwarding.valid2 = 0;
        forwarding.reg2 = 0;
        forwarding.val2 = 0;
    end
    if (complete3.valid) begin
        forwarding.valid3 = 1;
        forwarding.reg3 = complete3.rd;
        forwarding.val3 = complete3.result;
    end else begin
        forwarding.valid3 = 0;
        forwarding.reg3 = 0;
        forwarding.val3 = 0;
    end
end

integer i;
always_ff @ (posedge clk) begin
    if(reset) begin
        for (i = 0; i < 16; i = i + 1) begin 
            rob_table[i].valid <= 0;
            rob_table[i].pc <= 0;
            rob_table[i].rd <= 0;
            rob_table[i].rd_old <= 0;
            rob_table[i].result <= 0;
            rob_table[i].control.MemRead  <= '0;
            rob_table[i].control.MemtoReg <= '0;
            rob_table[i].control.ALUOp    <= '0;
            rob_table[i].control.MemWrite <= '0;
            rob_table[i].control.ALUSrc   <= '0;
            rob_table[i].control.RegWrite <= '0;   
        end
    end else begin
        if (dispatch.valid1) begin
            rob_table[dispatch.robNum1].valid <= 1;
            rob_table[dispatch.robNum1].pc <= dispatch.pc1;
            rob_table[dispatch.robNum1].rd <= dispatch.destReg1;
            rob_table[dispatch.robNum1].rd_old <= dispatch.destRegOld1;
            rob_table[dispatch.robNum1].control <= dispatch.control1;
        end
        if (dispatch.valid2) begin
            rob_table[dispatch.robNum2].valid <= 1;
            rob_table[dispatch.robNum2].pc <= dispatch.pc2;
            rob_table[dispatch.robNum2].rd <= dispatch.destReg2;
            rob_table[dispatch.robNum2].rd_old <= dispatch.destRegOld2;
            rob_table[dispatch.robNum2].control <= dispatch.control2;
        end
        if (complete1.valid) begin
            rob_table[complete1.robNum].result <= complete1.result;
        end
        if (complete2.valid) begin
            rob_table[complete2.robNum].result <= complete2.result;
        end

        




    end

end


endmodule