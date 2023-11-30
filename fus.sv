`timescale 1ns/1ps

import typedefs::aluStruct;
module fus (
input logic clk); // More needed

// Declare local nets to send to complete stage
aluStruct aluIn0;
aluStruct aluIn1;
logic [31:0] alu_out0;
logic [31:0] alu_out1;
logic flag_sign0;
logic flag_sign1;
logic flag_zero0;
logic flag_zero1;

// Need to assign the input struct here

alu fu0 (.clk, .aluStruct(aluStruct0), .alu_out(alu_out0), .flag_sign(flag_sign0), .flag_zero(flag_zero0));
alu fu1 (.clk, .aluStruct(aluStruct1), .alu_out(alu_out1), .flag_sign(flag_sign1), .flag_zero(flag_zero1));

endmodule