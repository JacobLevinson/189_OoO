`timescale 1ns/100ps

module reservationStation import typedefs::*; (
input logic clk,
input logic reset,
input rsEntry rsLine_a,
input rsEntry rsLine_b,
input logic[63:0] phy_reg_rdy,
input fuRdyStruct fuRdy,

//input forwardingStruct completeForward,
//input logic [15:0] robFree,

// These are wired to the regfile
output regReqStruct reg_request [2:0], // Combinational

// These are wired from the regfile
input regRespStruct reg_response [2:0], // Combinational

output rsIssue issue0,
output rsIssue issue1,
output rsIssue issue2
);
/*logic [63:0] physReg [31:0] = 0;
logic [3:0] firstRobFree;
logic [3:0] secondRobFree;
logic [3:0] robFreeSpace;*/

rsEntry rsTable [15:0];
logic [3:0] rs_idx; // Use this as a ptr to where to dispatch the next instruction

logic [3:0] rs_index_a;
logic [3:0] rs_index_b;

assign rs_index_a = rsLine_a.robNum;
assign rs_index_b = rsLine_b.robNum;

integer i;
always_ff @(posedge clk) begin
    if (reset) begin // Initialize the RS Table
        for (i = 0; i < 16; i = i + 1) begin
            rsTable[i].valid    <= '0;
            rsTable[i].src1rdy  <= '0;
            rsTable[i].src2rdy  <= '0;
            rsTable[i].fu       <= '0;
            rsTable[i].robNum   <= '0;
            rsTable[i].instruction.pc       <= '0;
            rsTable[i].instruction.opcode   <= '0;
            rsTable[i].instruction.rd       <= '0;
            rsTable[i].instruction.rs1      <= '0;
            rsTable[i].instruction.rs2      <= '0;
            rsTable[i].instruction.imm      <= '0;
            rsTable[i].instruction.ALUCtrl  <= '0;
            rsTable[i].instruction.control.MemRead  <= '0;
            rsTable[i].instruction.control.MemtoReg <= '0;
            rsTable[i].instruction.control.ALUOp    <= '0;
            rsTable[i].instruction.control.MemWrite <= '0;
            rsTable[i].instruction.control.ALUSrc   <= '0;
            rsTable[i].instruction.control.RegWrite <= '0;       
        end
    end else begin
        // Store the dispatch logic output to the RS table
        if (rsLine_a.valid) begin // Is the dispatch stage output even valid?
            rsTable[rs_index_a]       <= rsLine_a;
        end
        if (rsLine_b.valid) begin // Is the dispatch stage output even valid?
            rsTable[rs_index_b]      <= rsLine_b;
        end
        
        // Go through the entire RS Table and update all src_rdy signals
        // There should not be any dependencies because of renaming
        for (i = 0; i < 16; i = i + 1) begin
            if (rs_index_a != i && rs_index_b != i && rsTable[i].valid) begin 
                // Skip the src_rdy signals for the new RS table entries
                rsTable[i].src1rdy <= phy_reg_rdy[rsTable[i].instruction.rs1];
                rsTable[i].src2rdy <= rsTable[i].instruction.control.ALUSrc ? 1'b1 : phy_reg_rdy[rsTable[i].instruction.rs2]; 
                // This line checks that if we are to use an immediate, then ignore what is in the rs2 field for register readiness
            end
        end
    end
end

logic[15:0] validity; // This extracts all RS table valid states for easier use
assign validity = {rsTable[15].valid, rsTable[14].valid, rsTable[13].valid, rsTable[12].valid, 
                   rsTable[11].valid, rsTable[10].valid, rsTable[9].valid, rsTable[8].valid,
                   rsTable[7].valid, rsTable[5].valid, rsTable[5].valid, rsTable[4].valid, 
                   rsTable[3].valid, rsTable[2].valid, rsTable[1].valid, rsTable[0].valid};

logic [4:0] issue [1:0];

integer j;
always_comb begin 
    // This searches the RS table to find an entry it can issue
    // That is, entry is valid and all sources are ready and does not overlap with another entry's FU
    // This cascade of checks probably could be more efficient
    for (j = 0; j < 3; j = j + 1) begin // Search for an instruction for all 3 FUs, deal with the fact that FU2 (mem) might be busy in the sequential part
        if (validity) begin // If there is stuff in the RS table
            if (rsTable[rs_idx].valid && rsTable[rs_idx].src1rdy && rsTable[rs_idx].src2rdy && (rsTable[rs_idx].fu == j)) begin
                issue[j] = rs_idx;
            end else if (rsTable[rs_idx+1].valid && rsTable[rs_idx+1].src1rdy && rsTable[rs_idx+1].src2rdy && (rsTable[rs_idx+1].fu == j)) begin
                issue[j] = rs_idx + 1;
            end else if (rsTable[rs_idx+2].valid && rsTable[rs_idx+2].src1rdy && rsTable[rs_idx+2].src2rdy && (rsTable[rs_idx+2].fu == j)) begin
                issue[j] = rs_idx + 2;
            end else if (rsTable[rs_idx+3].valid && rsTable[rs_idx+3].src1rdy && rsTable[rs_idx+3].src2rdy && (rsTable[rs_idx+3].fu == j)) begin
                issue[j] = rs_idx + 3;
            end else if (rsTable[rs_idx+4].valid && rsTable[rs_idx+4].src1rdy && rsTable[rs_idx+4].src2rdy && (rsTable[rs_idx+4].fu == j)) begin
                issue[j] = rs_idx + 4;
            end else if (rsTable[rs_idx+5].valid && rsTable[rs_idx+5].src1rdy && rsTable[rs_idx+5].src2rdy && (rsTable[rs_idx+5].fu == j)) begin
                issue[j] = rs_idx + 5;
            end else if (rsTable[rs_idx+6].valid && rsTable[rs_idx+6].src1rdy && rsTable[rs_idx+6].src2rdy && (rsTable[rs_idx+6].fu == j)) begin
                issue[j] = rs_idx + 6;
            end else if (rsTable[rs_idx+7].valid && rsTable[rs_idx+7].src1rdy && rsTable[rs_idx+7].src2rdy && (rsTable[rs_idx+7].fu == j)) begin
                issue[j] = rs_idx + 7;
            end else if (rsTable[rs_idx+8].valid && rsTable[rs_idx+8].src1rdy && rsTable[rs_idx+8].src2rdy && (rsTable[rs_idx+8].fu == j)) begin
                issue[j] = rs_idx + 8;
            end else if (rsTable[rs_idx+9].valid && rsTable[rs_idx+9].src1rdy && rsTable[rs_idx+9].src2rdy && (rsTable[rs_idx+9].fu == j)) begin
                issue[j] = rs_idx + 9;
            end else if (rsTable[rs_idx+10].valid && rsTable[rs_idx+10].src1rdy && rsTable[rs_idx+10].src2rdy && (rsTable[rs_idx+10].fu == j)) begin
                issue[j] = rs_idx + 10;
            end else if (rsTable[rs_idx+11].valid && rsTable[rs_idx+11].src1rdy && rsTable[rs_idx+11].src2rdy && (rsTable[rs_idx+11].fu == j)) begin
                issue[j] = rs_idx + 11;
            end else if (rsTable[rs_idx+12].valid && rsTable[rs_idx+12].src1rdy && rsTable[rs_idx+12].src2rdy && (rsTable[rs_idx+12].fu == j)) begin
                issue[j] = rs_idx + 12;
            end else if (rsTable[rs_idx+13].valid && rsTable[rs_idx+13].src1rdy && rsTable[rs_idx+13].src2rdy && (rsTable[rs_idx+13].fu == j)) begin
                issue[j] = rs_idx + 13;
            end else if (rsTable[rs_idx+14].valid && rsTable[rs_idx+14].src1rdy && rsTable[rs_idx+14].src2rdy && (rsTable[rs_idx+14].fu == j)) begin
                issue[j] = rs_idx + 14;
            end else if (rsTable[rs_idx+15].valid && rsTable[rs_idx+15].src1rdy && rsTable[rs_idx+15].src2rdy && (rsTable[rs_idx+15].fu == j)) begin
                issue[j] = rs_idx + 15;
            end else begin
                issue[j] = '1; // No results found
            end
        end else begin
            issue[j] = '1;
        end
        // These will go to read the registers
        reg_request[j].RegWrite = '0; // No writing allowed outside of retire stage
        reg_request[j].rs1      = rsTable[issue[j][3:0]].instruction.rs1;
        reg_request[j].rs2      = rsTable[issue[j][3:0]].instruction.rs2;
        reg_request[j].rd       = '0; // No writing allowed outside of retire stage
        reg_request[j].wr_data  = '0; // No writing allowed outside of retire stage
    end
end
        

always_ff @(posedge clk) begin // Issue logic
    if (reset) begin
        rs_idx <= '0;
    end else begin
        if (issue[0] != 5'b1) begin // Checks that we found a valid entry
            issue0.valid    <= rsTable[issue[0][3:0]].valid;
            issue0.robNum   <= rsTable[issue[0][3:0]].robNum;
            issue0.pc       <= rsTable[issue[0][3:0]].instruction.pc;
            issue0.rd       <= rsTable[issue[0][3:0]].instruction.rd;
            issue0.rd_old   <= rsTable[issue[0][3:0]].instruction.rd_old;
            issue0.rs1      <= reg_response[0].rs1_data; // 32 bit data
            issue0.rs2      <= reg_response[0].rs2_data; // 32 bit data
            issue0.imm      <= rsTable[issue[0][3:0]].instruction.imm;
            issue0.ALUCtrl  <= rsTable[issue[0][3:0]].instruction.ALUCtrl;
            issue0.control  <= rsTable[issue[0][3:0]].instructions.control;
        end 
        if (issue[1] != 5'b1) begin // Checks that we found a valid entry
            issue1.valid    <= rsTable[issue[1][3:0]].valid;
            issue1.robNum   <= rsTable[issue[1][3:0]].robNum;
            issue1.pc       <= rsTable[issue[1][3:0]].instruction.pc;
            issue1.rd       <= rsTable[issue[1][3:0]].instruction.rd;
            issue1.rd_old   <= rsTable[issue[1][3:0]].instruction.rd_old;
            issue1.rs1      <= reg_response[1].rs1_data; // 32 bit data
            issue1.rs2      <= reg_response[1].rs2_data; // 32 bit data
            issue1.imm      <= rsTable[issue[1][3:0]].instruction.imm;
            issue1.ALUCtrl  <= rsTable[issue[1][3:0]].instruction.ALUCtrl;
            issue1.control  <= rsTable[issue[1][3:0]].instructions.control;
        end 
        if (fuRdy.mem) begin // First check that the FU is ready
            if (issue[1] != 5'b1) begin // Checks that we found a valid entry
                issue2.valid    <= rsTable[issue[2][3:0]].valid;
                issue2.robNum   <= rsTable[issue[2][3:0]].robNum;
                issue2.pc       <= rsTable[issue[2][3:0]].instruction.pc;
                issue2.rd       <= rsTable[issue[2][3:0]].instruction.rd;
                issue2.rd_old   <= rsTable[issue[2][3:0]].instruction.rd_old;
                issue2.rs1      <= reg_response[2].rs1_data; // 32 bit data
                issue2.rs2      <= reg_response[2].rs2_data; // 32 bit data
                issue2.imm      <= rsTable[issue[2][3:0]].instruction.imm;
                issue2.ALUCtrl  <= rsTable[issue[2][3:0]].instruction.ALUCtrl;
                issue2.control  <= rsTable[issue[2][3:0]].instructions.control;
            end 
            // Otherwise, do not issue and hold previous issue in registers
        end
    end
end
            

endmodule
/*
	// Dsipatch stage

	// If we have a valid instruction, dispatch it to the reservation station

	// Check if there is at least 2 free spots in the ROB by checking if there's at least 2 1's in robFree

	if($countones(robFree) < 2) begin // or other stall signals, we will wrap the rest of our code in this if statement
		//STALL
	end
	
	// Find the first free spot in ROB
	// Find the MSB that is set to 1
	automatic int temp = 0;
	for (int i = 15; i >= 0; i--) begin
		if (robFree[i] == 1'b1) begin
			firstRobFree <= i[3:0];
			temp = i[3:0];
			break;
		end
	end
	// Find the second free spot in ROB
	// Find the second MSB that is set to 1
	for (int i = temp - 1; i >= 0; i--) begin
		if (robFree[i] == 1'b1) begin
			secondRobFree <= i[3:0];
			break;
		end
	end


	// Dispatch the first instruction to the ROB and to the reservation station
	if(dispatchData.inst1valid) begin
		robDispatch.destReg1 <= dispatchData.inst1.rd;
		robDispatch.destRegOld1 <= dispatchData.destRegOld1;
		robDispatch.robNum1 <= firstRobFree;
		robDispatch.pc1 <= dispatchData.inst1.pc;
		robDispatch.valid1 <= 1;
		// Now dispatch to reservation station
		
		
	end else begin
		robDispatch.valid1 <= 0;
	end
	// Dispatch the second instruction to the ROB and to the reservation station
	if(dispatchData.inst2valid) begin
		robDispatch.destReg2 <= dispatchData.inst2.rd;
		robDispatch.destRegOld2 <= dispatchData.destRegOld2;
		robDispatch.robNum2 <= secondRobFree;
		robDispatch.pc2 <= dispatchData.inst2.pc;
		robDispatch.valid2 <= 1;
		// Now dispatch to reservation station
		
	end else begin
		robDispatch.valid2 <= 0;
	end

	


	// Forward outputs from complete stage to waiting registers and mark them as ready
	if(completeForward.valid1) begin
		physReg [completeForward.reg1] <= completeForward.val1;
		reservationTable [completeForward.reg1].src1rdy <= 1;
	end
	if(completeForward.valid2) begin
		physReg [completeForward.reg2] <= completeForward.val2;
		reservationTable [completeForward.reg2].src2rdy <= 1;
	end













end




endmodule*/