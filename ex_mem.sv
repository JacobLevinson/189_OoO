`timescale 1ns/1ps

import typedefs::aluStruct;
module ex_mem_addr (
input logic clk,
input aluStruct aluIn
// Put the memory request struct here
);

logic flag_zero;
logic flag_sign;
logic [31:0] alu_out;

alu calc_addr(.*);

endmodule
/*
module ex_mem_rd (
input logic [31:0]
);

endmodule*/