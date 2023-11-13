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
    logic [4:0] rs1;
    logic [4:0] rs2;
    logic [4:0] rd;
    logic [6:0] funct7;
    logic [2:0] funct3;
    logic [31:0] imm;
    ctrlStruct control;
} instStruct;







endmodule