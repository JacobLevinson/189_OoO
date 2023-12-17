`timescale 1ns/100ps

package typedefs;
localparam ROB_SIZE_BITS = 4;
typedef struct {
	logic [31:0] inst_a;
	logic [31:0] inst_b;
	logic [31:0] pc_a;
	logic [31:0] pc_b;
} fetchStruct;

typedef struct {
	logic MemRead;
	logic MemtoReg;
	logic [1:0] ALUOp;
	logic MemWrite;
	logic ALUSrc;
	logic RegWrite;
} ctrlStruct;

typedef struct { // Use this struct for architectural register addressing
	logic [31:0] pc;
	logic [6:0] opcode;
	logic [4:0] rd; // 5 bit architectural addressing
    logic [4:0] rs1;
    logic [4:0] rs2;
	logic [2:0] funct3;
    logic [6:0] funct7;
    logic [31:0] imm;
    ctrlStruct control;
} instStruct;

typedef struct { // Use this struct for physical register addressing
	logic [31:0] pc;
	logic [6:0] opcode;
	logic [5:0] rd; // 6 bit physical addressing
	logic [5:0] rd_old; // This is needed by the ROB to tell the rename stage to put this register in the free pool upon retire
    logic [5:0] rs1;
    logic [5:0] rs2;
    logic [31:0] imm;
    logic [3:0] ALUCtrl;
    ctrlStruct control;
} dispatchStruct;


typedef struct {
    logic valid;
    dispatchStruct instruction;
    // Flags
    logic src1rdy;
    logic [31:0] src1val;
    logic src2rdy;
    logic [31:0] src2val;
    logic [1:0] fu;
    logic [3:0] robNum;
} rsEntry;

typedef struct {
    logic alu1;
    logic alu2;
    logic mem;
} fuRdyStruct;

typedef struct {
    logic RegWrite; // Control signal
    logic [6:0] rs1; // Physical
    logic [6:0] rs2; // Physical
    logic [6:0] rd; // Physical
    logic [31:0] wr_data; // Data to write
} regReqStruct;

typedef struct {
    logic [31:0] rs1_data;
    logic [31:0] rs2_data;
} regRespStruct;

typedef struct {
    logic valid;
    logic [3:0] robNum;
	logic [31:0] pc;
	logic [5:0] rd; // 6 bit physical addressing
	logic [5:0] rd_old; // This is needed by the ROB to tell the rename stage to put this register in the free pool upon retire
    logic [31:0] rs1;
    logic [31:0] rs2;
    logic [31:0] imm;
    logic [3:0] ALUCtrl;
    ctrlStruct control;
} rsIssue;

typedef struct {
    logic [31:0] rs1;
    logic [31:0] rs2;
    logic [31:0] imm;
    logic [3:0] ALUCtrl;
	logic ALUSrc;
	logic valid;
} aluInStruct;

typedef struct {
    logic[31:0] result;
    logic flag_sign;
    logic flag_zero;
    logic valid;
} aluOutStruct;


typedef struct {
	logic [31:0] addr;
	logic [31:0] wr_data;
	logic MemWrite;
	logic MemRead;
	logic valid;
} memReqStruct;

typedef struct {
    logic [31:0] rd_data;
    logic MemWrite;
	logic MemRead;
    logic valid;
} memRespStruct;

typedef struct {
    logic valid;
    logic [3:0] robNum;
	logic [31:0] pc;
	logic [5:0] rd; // 6 bit physical addressing
	logic [5:0] rd_old; // This is needed by the ROB to tell the rename stage to put this register in the free pool upon retire
    logic [31:0] result;
    logic [31:0] mem_data;
    ctrlStruct control;
} completeStruct;



typedef struct {
    logic valid1;
    logic valid2;
    logic valid3;
    logic [5:0] reg1;
    logic [5:0] reg2;
    logic [5:0] reg3;
    logic [31:0] val1;
    logic [31:0] val2;
    logic [31:0] val3;
} forwardingStruct;

typedef struct {
    logic [5:0] destReg1;
    logic [5:0] destRegOld1;
    logic [5:0] robNum1;
    ctrlStruct control1;
    logic [31:0] pc1;
    logic valid1;
    logic [5:0] destReg2;
    logic [5:0] destRegOld2;
    logic [5:0] robNum2;
    ctrlStruct control2;
    logic [31:0] pc2;
    logic valid2;
} robDispatchStruct;

typedef struct {
    logic valid;
    logic complete;
    logic [31:0] pc;
    logic [5:0] rd; // 6 bit physical addressing
    logic [5:0] rd_old; // This is needed by the ROB to tell the rename stage to put this register in the free pool upon retire
    logic [31:0] result;
    logic [31:0] mem_data;
    ctrlStruct control;
} robEntryStruct;



endpackage : typedefs