package typedefs;

typedef struct {
	logic [31:0] inst_a;
	logic [31:0] inst_b;
	logic [31:0] pc_a;
	logic [31:0] pc_b;
} fetch_decode;

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
	logic [2:0] funct3;
   logic [6:0] funct7;
   logic [31:0] imm;
   ctrlStruct control;
} dispatchStruct;

endpackage : typedefs