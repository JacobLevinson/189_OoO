module ex_mem_addr (
input logic [31:0] rs1,
input logic [31:0] rs2,
input logic [31:0] imm,
input logic [3:0] ALU_ctrl,
input logic ALUSrc,
output logic [31:0] alu_out
);

logic flag_zero;
logic flag_sign;

alu calc_addr(.*);

endmodule
/*
module ex_mem_rd (
input logic [31:0]
);

endmodule*/