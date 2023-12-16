`timescale 1ns/100ps

module fus import typedefs::*; (
input logic clk,

input rsIssue issue0,
input rsIssue issue1,
output completeStruct complete0,
output completeStruct complete1,

input rsIssue issue2,
output memReqStruct request,
input memRespStruct response,
output completeStruct complete2
);

// Signals needed for ALU
aluInStruct aluIn0;
aluInStruct aluIn1;

// Parse issue struct into alu struct
assign aluIn0.rs1       = issue0.rs1;
assign aluIn0.rs2       = issue0.rs2;
assign aluIn0.imm       = issue0.imm;
assign aluIn0.ALUCtrl   = issue0.ALUCtrl;
assign aluIn0.ALUSrc    = issue0.ALUSrc;
assign aluIn0.valid     = issue0.valid;

assign aluIn1.rs1       = issue1.rs1;
assign aluIn1.rs2       = issue1.rs2;
assign aluIn1.imm       = issue1.imm;
assign aluIn1.ALUCtrl   = issue1.ALUCtrl;
assign aluIn1.ALUSrc    = issue1.ALUSrc;
assign aluIn1.valid     = issue1.valid;

aluOutStruct aluOut0;
aluOutStruct aluOut1;

alu FU0(.clk, .aluIn(aluIn0), .aluOut(aluOut0)); // Combinational except for assertion
alu FU1(.clk, .aluIn(aluIn1), .aluOut(aluOut1)); // Combinational except for assertion

always_ff @(posedge clk) begin // Push to pipeline registers
    complete0.valid     <= aluOut0.valid;
    complete0.robNum    <= issue0.robNum;
    complete0.pc        <= issue0.pc;
    complete0.rd        <= issue0.rd;
    complete0.rd_old    <= issue0.rd_old;
    complete0.result    <= aluOut0.result;
    complete0.control   <= issue0.control;
    
    complete1.valid     <= aluOut1.valid;
    complete1.robNum    <= issue1.robNum;
    complete1.pc        <= issue1.pc;
    complete1.rd        <= issue1.rd;
    complete1.rd_old    <= issue1.rd_old;
    complete1.result    <= aluOut1.result;
    complete1.control   <= issue1.control;
end

// Mem FU
aluInStruct aluIn2;

// Parse issue struct into alu struct
assign aluIn2.rs1       = issue2.rs1;
assign aluIn2.rs2       = issue2.rs2;
assign aluIn2.imm       = issue2.imm;
assign aluIn2.ALUCtrl   = issue2.ALUCtrl;
assign aluIn2.ALUSrc    = issue2.ALUSrc;
assign aluIn2.valid     = issue2.valid;

aluOutStruct aluOut2;

alu MEM(.clk, .aluIn(aluIn2), .aluOut(aluOut2)); // Combinational except for assertions

always_ff @ (posedge clk) begin // Package the memory request
    request.addr        <= aluOut2.result;
    request.wr_data     <= issue2.rs2;
    request.MemWrite    <= '0; // Don't write here, only read
    request.MemRead     <= issue2.control.MemRead;
    request.valid       <= aluOut2.valid;
end

always_ff @ (posedge clk) begin // Output the memory response as registers
    complete2.valid     <= response.valid;
    complete2.robNum    <= issue2.robNum;
    complete2.pc        <= issue2.pc;
    complete2.rd        <= issue2.rd;
    complete2.rd_old    <= issue2.rd_old;
    if (response.MemRead) begin
        complete2.result    <= response.rd_data; // This is what we just read
    end else begin
        complete2.result    <= issue2.rs2; // Put what we will need to commit to memory in the result
    end
    complete2.control   <= issue2.control;
end

endmodule