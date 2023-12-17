`timescale 1ns/100ps

module retire import typedefs::*;(
    input robEntryStruct rob_entry1,
    input robEntryStruct rob_entry2,
    output regReqStruct regReqest1,
    output regReqStruct regReqest2,
    output memReqStruct memRequest1,
    output memReqStruct memRequest2,
    output freeRegStruct freeReg
);

always_comb begin
    if(rob_entry1.valid) begin
        if(rob_entry1.control.MemWrite) begin
            regReqest1.RegWrite = '0;
            memRequest1.valid = 1;
            memRequest1.addr = rob_entry1.result;
            memRequest1.wr_data = rob_entry1.mem_data;
            freeReg.valid1 = '0;
            freeReg.reg1 ='0;
        end else begin
            regReqest1.RegWrite = 1;
            memRequest1.valid = '0;
            regReqest1.rd = rob_entry1.rd;
            regReqest1.wr_data = rob_entry1.result;
            freeReg.valid = 1;
            freeReg.reg1 = rob_entry1.rd_old;
        end
    end
    if(rob_entry2.valid) begin
        if(rob_entry2.control.MemWrite) begin
            regReqest2.RegWrite = '0;
            memRequest2.valid = 1;
            memRequest2.addr = rob_entry2.result;
            memRequest2.wr_data = rob_entry2.mem_data;
            freeReg.valid2 = '0;
            freeReg.reg2 ='0;
        end else begin
            regReqest2.RegWrite = 1;
            memRequest2.valid = '0;
            regReqest2.rd = rob_entry2.rd;
            regReqest2.wr_data = rob_entry2.result;
            freeReg.valid2 = 1;
            freeReg.reg2 = rob_entry2.rd_old;
        end
    end

end



endmodule