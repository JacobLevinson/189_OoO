`timescale 1ns/1ps
module 189_OoO 


typedef struct {
    logic MemRead;
    logic MemtoReg;
    logic [1:0] ALUOp;
    logic MemtoReg;
    logic MemWrite;
    logic ALUSrc;
    logic RegWrite;
} ctrlStruct;


typedef struct {
    logic [31:0] pc;
    logic [6:0] opcode;
    logic [5:0] rs1;
    logic [5:0] rs2;
    logic [5:0] rd;
    logic [6:0] funct7;
    logic [2:0] funct3;
    logic [31:0] imm;
    ctrlStruct control;
} instStruct;

parameter ROB_SIZE_BITS = 4;

typedef struct {
    logic use;
    instStruct instruction;
    logic src1rdy;
    logic src2rdy;
    logic src2rdy;
    logic [1:0] fu;
    logic [ROB_SIZE_BITS-1:0] robNum;
} reservationStationEntry;

typedef struct {
    logic valid1;
    logic valid2;
    logic [5:0] reg1;
    logic [5:0] reg2;
    logic [31:0] val1;
    logic [31:0] val2;
} forwardingStruct;

typedef struct {
    logic alu1;
    logic alu2;
    logic mem;
} fuRdyStruct;

typedef struct {
	instStruct inst1;
    logic [5:0] destRegOld1;
	logic inst1valid;
	instStruct inst2;
    logic [5:0] destRegOld2;
	logic inst2valid;
} dispatchStruct;

typedef struct {
    logic [31:0] input1;
    logic [31:0] input2;
    logic valid;
} aluInputStruct;

typedef struct {
    logic [31:0] addr;
    logic valid;
} memReadInputStruct;

typedef struct {
    logic [31:0] value;
    logic valid;
} memReadOutputStruct;

typedef struct {
    logic [5:0] destReg1;
    logic [5:0] destRegOld1;
    logic [5:0] robNum1;
    logic [31:0] pc1;
    logic valid1;
    logic [5:0] destReg2;
    logic [5:0] destRegOld2;
    logic [5:0] robNum2;
    logic [31:0] pc2;
    logic valid2;
} robDispatchStruct;

endmodule