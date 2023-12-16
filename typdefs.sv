package typedefs;
parameter ROB_SIZE_BITS = 4;
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

typedef struct {
   logic [31:0] rs1;
   logic [31:0] rs2;
	logic [31:0] imm;
   logic [3:0] ALU_ctrl;
	logic ALUSrc;
} aluStruct;

typedef struct {
	logic [31:0] addr;
	logic [31:0] wr_data;
	logic MemWrite;
	logic MemRead;
} memReqStruct;

typedef struct {
    logic [31:0] rd_data;
    logic valid;
} memRespStruct;

typedef struct {
    logic useBit;
    instStruct instruction;
    logic src1rdy;
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

typedef struct { // Use this struct for physical register addressing
	instStruct inst1;
    logic [5:0] destRegOld1;  // This is needed by the ROB to tell the rename stage to put this register in the free pool upon retire
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


typedef struct {
	logic [31:0] address;
} memReadInputStruct;

typedef struct {
	logic [31:0] data;
	logic ready;
} memReadOutputStruct;
endpackage : typedefs