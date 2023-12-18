`timescale 1ns/100ps

module retire import typedefs::*;(
input logic clk, // For assertions only
input robEntryStruct retire_instr_a,
input robEntryStruct retire_instr_b,
output regReqStruct regReqest_a,
output regReqStruct regReqest_b,
output memReqStruct memRequest_a,
output memReqStruct memRequest_b,
input memRespStruct memResponse_a,
input memRespStruct memResponse_b,
output forwardingStruct forward_a,
output forwardingStruct forward_b,
output freeRegStruct freeReg_a,
output freeRegStruct freeReg_b
);

always_comb begin
    if(retire_instr_a.valid) begin
        if(retire_instr_a.control.MemWrite) begin // Instriction we are going to retire requires a memory write          
            regReqest_a.RegWrite    = '0; // Don't request from registers
            regReqest_a.rs1         = '0;
            regReqest_a.rs2         = '0;
            regReqest_a.rd          = '0;
            regReqest_a.wr_data     = '0;
            
            memRequest_a.addr       = retire_instr_a.result; // Make memory request
            memRequest_a.wr_data    = retire_instr_a.wr_data;
            memRequest_a.MemWrite   = '1;
            memRequest_a.MemRead    = '0;
            memRequest_a.valid      = '1;
            
            freeReg_a.valid     = '0; // Don't free registers on a memory write, no destination registers
            freeReg_a.reg_addr  = '0;
            
            forward_a.valid     = '0;
            forward_a.reg_addr  = '0;
            forward_a.data      = '0;
        end else if (retire_instr_a.control.MemtoReg) begin // For LWs            
            regReqest_a.RegWrite    = '1; 
            regReqest_a.rs1         = '0;
            regReqest_a.rs2         = '0;
            regReqest_a.rd          = retire_instr_a.rd;
            regReqest_a.wr_data     = memResponse_a.rd_data;
            
            memRequest_a.addr       = retire_instr_a.result; 
            memRequest_a.wr_data    = '0;
            memRequest_a.MemWrite   = '0;
            memRequest_a.MemRead    = '1;
            memRequest_a.valid      = '1;
            
            freeReg_a.valid     = '1; 
            freeReg_a.reg_addr  = retire_instr_a.rd_old;
            
            forward_a.valid     = '1;
            forward_a.reg_addr  = retire_instr_a.rd;
            forward_a.data      = memResponse_a.rd_data;
        end else if (retire_instr_a.control.RegWrite) begin // Instrction we are going to retire requires a register write
            regReqest_a.RegWrite    = '1; 
            regReqest_a.rs1         = '0;
            regReqest_a.rs2         = '0;
            regReqest_a.rd          = retire_instr_a.rd;
            regReqest_a.wr_data     = retire_instr_a.result;
            
            memRequest_a.addr       = '0; 
            memRequest_a.wr_data    = '0;
            memRequest_a.MemWrite   = '0;
            memRequest_a.MemRead    = '0;
            memRequest_a.valid      = '0;
            
            freeReg_a.valid     = '1; // Free register upon retire
            freeReg_a.reg_addr  = retire_instr_a.rd_old;
            
            forward_a.valid     = '0;
            forward_a.reg_addr  = '0;
            forward_a.data      = '0;
        end else begin // Something broken do absolutely nothing
            regReqest_a.RegWrite    = '0; // Do nothing
            regReqest_a.rs1         = '0;
            regReqest_a.rs2         = '0;
            regReqest_a.rd          = '0;
            regReqest_a.wr_data     = '0;
            
            memRequest_a.addr       = '0; // Do nothing
            memRequest_a.wr_data    = '0;
            memRequest_a.MemWrite   = '0;
            memRequest_a.MemRead    = '0;
            memRequest_a.valid      = '0;
            
            freeReg_a.valid     = '0; // Do nothing
            freeReg_a.reg_addr  = '0;
            
            forward_a.valid     = '0;
            forward_a.reg_addr  = '0;
            forward_a.data      = '0;
        end
    end else begin // No instruction, do absolutely nothing
        regReqest_a.RegWrite    = '0; // Do nothing
        regReqest_a.rs1         = '0;
        regReqest_a.rs2         = '0;
        regReqest_a.rd          = '0;
        regReqest_a.wr_data     = '0;
            
        memRequest_a.addr       = '0; // Do nothing
        memRequest_a.wr_data    = '0;
        memRequest_a.MemWrite   = '0;
        memRequest_a.MemRead    = '0;
        memRequest_a.valid      = '0;
            
        freeReg_a.valid     = '0; // Do nothing
        freeReg_a.reg_addr  = '0;
        
        forward_a.valid     = '0;
        forward_a.reg_addr  = '0;
        forward_a.data      = '0;
    end
end

always_comb begin
    if(retire_instr_b.valid) begin
        if(retire_instr_b.control.MemWrite) begin // Instriction we are going to retire requires a memory write
            regReqest_b.RegWrite    = '0; // Don't request from registers
            regReqest_b.rs1         = '0;
            regReqest_b.rs2         = '0;
            regReqest_b.rd          = '0;
            regReqest_b.wr_data     = '0;
            
            memRequest_b.addr       = retire_instr_b.result; // Make memory request
            memRequest_b.wr_data    = retire_instr_b.wr_data;
            memRequest_b.MemWrite   = '1;
            memRequest_b.MemRead    = '0;
            memRequest_b.valid      = '1;
            
            freeReg_b.valid     = '0; // Don't free registers on a memory write, no destination registers
            freeReg_b.reg_addr  = '0;
            
            forward_b.valid     = '0;
            forward_b.reg_addr  = '0;
            forward_b.data      = '0;
        end else if (retire_instr_b.control.MemtoReg) begin // For LWs            
            regReqest_b.RegWrite    = '1; // Don't request from registers
            regReqest_b.rs1         = '0;
            regReqest_b.rs2         = '0;
            regReqest_b.rd          = retire_instr_b.rd;
            regReqest_b.wr_data     = memResponse_b.rd_data;
            
            memRequest_b.addr       = retire_instr_a.result; // Make memory request
            memRequest_b.wr_data    = '0;
            memRequest_b.MemWrite   = '0;
            memRequest_b.MemRead    = '1;
            memRequest_b.valid      = '1;
            
            freeReg_b.valid     = '1; 
            freeReg_b.reg_addr  = retire_instr_b.rd_old;
            
            forward_b.valid     = '1;
            forward_b.reg_addr  = retire_instr_b.rd;
            forward_b.data      = memResponse_b.rd_data;
        end else if (retire_instr_b.control.RegWrite) begin // Instrction we are going to retire requires a register write
            regReqest_b.RegWrite    = '1; // Don't request from registers
            regReqest_b.rs1         = '0;
            regReqest_b.rs2         = '0;
            regReqest_b.rd          = retire_instr_b.rd;
            regReqest_b.wr_data     = retire_instr_b.result;
            
            memRequest_b.addr       = '0; // Don't request from memory
            memRequest_b.wr_data    = '0;
            memRequest_b.MemWrite   = '0;
            memRequest_b.MemRead    = '0;
            memRequest_b.valid      = '0;
            
            freeReg_b.valid     = '1; // Free register upon retire
            freeReg_b.reg_addr  = retire_instr_a.rd_old;
            
            forward_b.valid     = '0;
            forward_b.reg_addr  = '0;
            forward_b.data      = '0;
        end else begin // Something broken do absolutely nothing
            regReqest_b.RegWrite    = '0; // Do nothing
            regReqest_b.rs1         = '0;
            regReqest_b.rs2         = '0;
            regReqest_b.rd          = '0;
            regReqest_b.wr_data     = '0;
            
            memRequest_b.addr       = '0; // Do nothing
            memRequest_b.wr_data    = '0;
            memRequest_b.MemWrite   = '0;
            memRequest_b.MemRead    = '0;
            memRequest_b.valid      = '0;
            
            freeReg_b.valid     = '0; // Do nothing
            freeReg_b.reg_addr  = '0;
            
            forward_b.valid     = '0;
            forward_b.reg_addr  = '0;
            forward_b.data      = '0;
        end
    end else begin // No instruction, do absolutely nothing
        regReqest_b.RegWrite    = '0; // Do nothing
        regReqest_b.rs1         = '0;
        regReqest_b.rs2         = '0;
        regReqest_b.rd          = '0;
        regReqest_b.wr_data     = '0;
            
        memRequest_b.addr       = '0; // Do nothing
        memRequest_b.wr_data    = '0;
        memRequest_b.MemWrite   = '0;
        memRequest_b.MemRead    = '0;
        memRequest_b.valid      = '0;
            
        freeReg_b.valid     = '0; // Do nothing
        freeReg_b.reg_addr  = '0;
        
        forward_b.valid     = '0;
        forward_b.reg_addr  = '0;
        forward_b.data      = '0;
    end
end

property require_writeback_a;
    @(posedge clk) disable iff (!retire_instr_a.valid)
    (retire_instr_a.control.MemWrite || retire_instr_a.control.RegWrite);
endproperty

assert property (require_writeback_a);

property require_writeback_b;
    @(posedge clk) disable iff (!retire_instr_b.valid)
    (retire_instr_b.control.MemWrite || retire_instr_b.control.RegWrite);
endproperty

assert property (require_writeback_b);

endmodule