`timescale 1ns/1ps
module OoO_189(
output logic clk,
output logic reset
);
import typedefs::*; // Quartus is dumb and only supports SV 2005, need SV 2009 to import this in the module header :(((

initial begin
	clk = 0;
	reset = 1;
	repeat(250) begin // Apparently we can't use forever loops??
		reset = 0;
		#10 clk = !clk;
	end
end

logic [31:0] pc; // Global PC, no jumping

always_ff @ (posedge clk) begin
	pc <= pc + 32'd8;
end


fetchStruct fd_reg; // Pipeline Register
fetch f_stage(.clk, .pc, .fd_reg);

instStruct dec_ren_reg_a; // Pipeline Register
instStruct dec_ren_reg_b; // Pipeline Register
decode(.clk, .fd_reg, .dec_ren_reg_a, .dec_ren_reg_b);

dispatchStruct ren_disp_reg_a; // Pipeline Register
dispatchStruct ren_disp_reg_b; // Pipeline Register
rename(.clk, .reset, .dec_ren_reg_a, .dec_ren_reg_b, .ren_disp_reg_a, .ren_disp_reg_b);

// Reservation Station Here

/*
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
*/

endmodule