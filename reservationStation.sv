`timescale 1ns/100ps

module reservationStation import typedefs::*; (
input logic clk,
input logic reset,
input rsEntry rsLine_a,
input rsEntry rsLine_b,

input forwardingStruct forward_a,
input forwardingStruct forward_b,
input forwardingStruct forward_c,

output rsIssue issue0,
output rsIssue issue1,
output rsIssue issue2
);

rsEntry rsTable [15:0];
logic [3:0] rs_idx; // Use this as a ptr to where to dispatch the next instruction
                        
logic [4:0] issue [2:0];

logic [3:0] rs_index_a;
logic [3:0] rs_index_b;

assign rs_index_a = rsLine_a.robNum;
assign rs_index_b = rsLine_b.robNum;

integer i;
always_ff @(posedge clk) begin
    if (reset) begin // Initialize the RS Table
        for (i = 0; i < 16; i = i + 1) begin
            rsTable[i].valid    <= '0;
            rsTable[i].rs1_rdy  <= '0;
            rsTable[i].rs2_rdy  <= '0;
            rsTable[i].rs1_data <= '0;
            rsTable[i].rs2_data <= '0;
            rsTable[i].fu       <= '0;
            rsTable[i].robNum   <= '0;
            rsTable[i].instruction.pc       <= '0;
            rsTable[i].instruction.opcode   <= '0;
            rsTable[i].instruction.rd       <= '0;
            rsTable[i].instruction.rd_old   <= '0;
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
        rs_idx <= '0; // Points to first free entry in the RS table        
    end else begin
        if (rsLine_a.valid && rsLine_b.valid) begin
            rs_idx <= rs_idx + 2'b10;
        end else if (rsLine_a.valid || rsLine_b.valid) begin
            rs_idx <= rs_idx + 1'b1;
        end
        // Go through the entire RS Table and update all register fields from the complete stage
        // There should not be any dependencies because of renaming
        for (i = 0; i < 16; i = i + 1) begin
            if (rs_index_a != i && rs_index_b != i && rsTable[i].valid) begin // Avoids multiple drivers
                if (forward_a.valid) begin
                    if (rsTable[i].instruction.rs1 == forward_a.reg_addr) begin
                        rsTable[i].rs1_rdy  <= '1;
                        rsTable[i].rs1_data <= forward_a.data;
                    end
                    
                    if (rsTable[i].instruction.rs2 == forward_a.reg_addr) begin
                        rsTable[i].rs2_rdy  <= '1;
                        rsTable[i].rs2_data <= forward_a.data;
                    end
                end
                
                if (forward_b.valid) begin
                    if (rsTable[i].instruction.rs1 == forward_b.reg_addr) begin
                        rsTable[i].rs1_rdy  <= '1;
                        rsTable[i].rs1_data <= forward_b.data;
                    end
                    
                    if (rsTable[i].instruction.rs2 == forward_b.reg_addr) begin
                        rsTable[i].rs2_rdy  <= '1;
                        rsTable[i].rs2_data <= forward_b.data;
                    end
                end
                
                if (forward_c.valid) begin
                    if (rsTable[i].instruction.rs1 == forward_c.reg_addr) begin
                        rsTable[i].rs1_rdy  <= '1;
                        rsTable[i].rs1_data <= forward_c.data;
                    end
                    
                    if (rsTable[i].instruction.rs2 == forward_c.reg_addr) begin
                        rsTable[i].rs2_rdy  <= '1;
                        rsTable[i].rs2_data <= forward_c.data;
                    end
                end
                
                if (issue[0] == i) begin
                    rsTable[i].valid    <= '0;
                    rsTable[i].rs1_rdy  <= '0;
                    rsTable[i].rs2_rdy  <= '0;
                    rsTable[i].rs1_data <= '0;
                    rsTable[i].rs2_data <= '0;
                    rsTable[i].fu       <= '0;
                    rsTable[i].robNum   <= '0;
                    rsTable[i].instruction.pc       <= '0;
                    rsTable[i].instruction.opcode   <= '0;
                    rsTable[i].instruction.rd       <= '0;
                    rsTable[i].instruction.rd_old   <= '0;
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
                
                if (issue[1] == i) begin
                    rsTable[i].valid    <= '0;
                    rsTable[i].rs1_rdy  <= '0;
                    rsTable[i].rs2_rdy  <= '0;
                    rsTable[i].rs1_data <= '0;
                    rsTable[i].rs2_data <= '0;
                    rsTable[i].fu       <= '0;
                    rsTable[i].robNum   <= '0;
                    rsTable[i].instruction.pc       <= '0;
                    rsTable[i].instruction.opcode   <= '0;
                    rsTable[i].instruction.rd       <= '0;
                    rsTable[i].instruction.rd_old   <= '0;
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
                
                if (issue[2] == i) begin
                    rsTable[i].valid    <= '0;
                    rsTable[i].rs1_rdy  <= '0;
                    rsTable[i].rs2_rdy  <= '0;
                    rsTable[i].rs1_data <= '0;
                    rsTable[i].rs2_data <= '0;
                    rsTable[i].fu       <= '0;
                    rsTable[i].robNum   <= '0;
                    rsTable[i].instruction.pc       <= '0;
                    rsTable[i].instruction.opcode   <= '0;
                    rsTable[i].instruction.rd       <= '0;
                    rsTable[i].instruction.rd_old   <= '0;
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
            end
            
            if (rs_index_a == i) begin 
                if (rsLine_a.valid) begin // Is the dispatch stage output even valid?
                    rsTable[rs_index_a]       <= rsLine_a; // Store the dispatch logic output to the RS table
                end
            end else if (rs_index_b == i) begin
                if (rsLine_b.valid) begin // Is the dispatch stage output even valid?
                    rsTable[rs_index_b]      <= rsLine_b; // Store the dispatch logic output to the RS table
                end
            end    
        end
    end
end

logic[15:0] validity; // This extracts all RS table valid states for easier use
assign validity = {rsTable[15].valid, rsTable[14].valid, rsTable[13].valid, rsTable[12].valid, 
                   rsTable[11].valid, rsTable[10].valid, rsTable[9].valid, rsTable[8].valid,
                   rsTable[7].valid, rsTable[5].valid, rsTable[5].valid, rsTable[4].valid, 
                   rsTable[3].valid, rsTable[2].valid, rsTable[1].valid, rsTable[0].valid};

integer j;
always_comb begin 
    // This searches the RS table to find an entry it can issue
    // That is, entry is valid and all sources are ready and does not overlap with another entry's FU
    // This cascade of checks probably could be more efficient
    for (j = 0; j < 3; j = j + 1) begin // Search for an instruction for all 3 FUs, deal with the fact that FU2 (mem) might be busy in the sequential part
        if (validity) begin // If there is stuff in the RS table
            if (rsTable[rs_idx].valid && rsTable[rs_idx].rs1_rdy && rsTable[rs_idx].rs2_rdy && (rsTable[rs_idx].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0]};
            end else if (rsTable[rs_idx[3:0]+4'd1].valid && rsTable[rs_idx[3:0]+4'd1].rs1_rdy && rsTable[rs_idx[3:0]+4'd1].rs2_rdy && (rsTable[rs_idx[3:0]+4'd1].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd1};
            end else if (rsTable[rs_idx[3:0]+4'd2].valid && rsTable[rs_idx[3:0]+4'd2].rs1_rdy && rsTable[rs_idx[3:0]+4'd2].rs2_rdy && (rsTable[rs_idx[3:0]+4'd2].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd2};
            end else if (rsTable[rs_idx[3:0]+4'd3].valid && rsTable[rs_idx[3:0]+4'd3].rs1_rdy && rsTable[rs_idx[3:0]+4'd3].rs2_rdy && (rsTable[rs_idx[3:0]+4'd3].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd3};
            end else if (rsTable[rs_idx[3:0]+4'd4].valid && rsTable[rs_idx[3:0]+4'd4].rs1_rdy && rsTable[rs_idx[3:0]+4'd4].rs2_rdy && (rsTable[rs_idx[3:0]+4'd4].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd4};
            end else if (rsTable[rs_idx[3:0]+4'd5].valid && rsTable[rs_idx[3:0]+4'd5].rs1_rdy && rsTable[rs_idx[3:0]+4'd5].rs2_rdy && (rsTable[rs_idx[3:0]+4'd5].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd5};
            end else if (rsTable[rs_idx[3:0]+4'd6].valid && rsTable[rs_idx[3:0]+4'd6].rs1_rdy && rsTable[rs_idx[3:0]+4'd6].rs2_rdy && (rsTable[rs_idx[3:0]+4'd6].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd6};
            end else if (rsTable[rs_idx[3:0]+4'd7].valid && rsTable[rs_idx[3:0]+4'd7].rs1_rdy && rsTable[rs_idx[3:0]+4'd7].rs2_rdy && (rsTable[rs_idx[3:0]+4'd7].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd7};
            end else if (rsTable[rs_idx[3:0]+4'd8].valid && rsTable[rs_idx[3:0]+4'd8].rs1_rdy && rsTable[rs_idx[3:0]+4'd8].rs2_rdy && (rsTable[rs_idx[3:0]+4'd8].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd8};
            end else if (rsTable[rs_idx[3:0]+4'd9].valid && rsTable[rs_idx[3:0]+4'd9].rs1_rdy && rsTable[rs_idx[3:0]+4'd9].rs2_rdy && (rsTable[rs_idx[3:0]+4'd9].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd9};
            end else if (rsTable[rs_idx[3:0]+4'd10].valid && rsTable[rs_idx[3:0]+4'd10].rs1_rdy && rsTable[rs_idx[3:0]+4'd10].rs2_rdy && (rsTable[rs_idx[3:0]+4'd10].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd10};
            end else if (rsTable[rs_idx[3:0]+4'd11].valid && rsTable[rs_idx[3:0]+4'd11].rs1_rdy && rsTable[rs_idx[3:0]+4'd11].rs2_rdy && (rsTable[rs_idx[3:0]+4'd11].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd11};
            end else if (rsTable[rs_idx[3:0]+4'd12].valid && rsTable[rs_idx[3:0]+4'd12].rs1_rdy && rsTable[rs_idx[3:0]+4'd12].rs2_rdy && (rsTable[rs_idx[3:0]+4'd12].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd12};
            end else if (rsTable[rs_idx[3:0]+4'd13].valid && rsTable[rs_idx[3:0]+4'd13].rs1_rdy && rsTable[rs_idx[3:0]+4'd13].rs2_rdy && (rsTable[rs_idx[3:0]+4'd13].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd13};
            end else if (rsTable[rs_idx[3:0]+4'd14].valid && rsTable[rs_idx[3:0]+4'd14].rs1_rdy && rsTable[rs_idx[3:0]+4'd14].rs2_rdy && rsTable[rs_idx[3:0]+4'd14].fu == j) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd14};
            end else if (rsTable[rs_idx[3:0]+4'd15].valid && rsTable[rs_idx[3:0]+4'd15].rs1_rdy && rsTable[rs_idx[3:0]+4'd15].rs2_rdy && (rsTable[rs_idx[3:0]+4'd15].fu == j)) begin
                issue[j] = {'0, rs_idx[3:0] + 4'd15};
            end else begin
                issue[j] = '1; // No results found
            end
        end else begin
            issue[j] = '1;
        end
    end
end
        
fuRdyStruct fuRdy;

assign fuRdy.alu1 = '1; // Can always issue to alu FUs because they are only 1 cycle
assign fuRdy.alu2 = '1;

always_ff @(posedge clk) begin // Issue logic
    if (reset) begin
        rs_idx <= '0;
    end else begin
        if (issue[0] != 5'b11111) begin // Checks that we found a valid entry
            issue0.valid    <= rsTable[issue[0][3:0]].valid;
            issue0.robNum   <= rsTable[issue[0][3:0]].robNum;
            issue0.pc       <= rsTable[issue[0][3:0]].instruction.pc;
            issue0.rd       <= rsTable[issue[0][3:0]].instruction.rd;
            issue0.rd_old   <= rsTable[issue[0][3:0]].instruction.rd_old;
            issue0.rs1      <= rsTable[issue[0][3:0]].rs1_data;
            issue0.rs2      <= rsTable[issue[0][3:0]].rs2_data;
            issue0.imm      <= rsTable[issue[0][3:0]].instruction.imm;
            issue0.ALUCtrl  <= rsTable[issue[0][3:0]].instruction.ALUCtrl;
            issue0.control  <= rsTable[issue[0][3:0]].instruction.control;
        end else begin
            issue0.valid    <= '0;
            issue0.robNum   <= '0;
            issue0.pc       <= '0;
            issue0.rd       <= '0;
            issue0.rd_old   <= '0;
            issue0.rs1      <= '0;
            issue0.rs2      <= '0;
            issue0.imm      <= '0;
            issue0.ALUCtrl  <= '0;
            issue0.control.MemRead  <= '0;
            issue0.control.MemtoReg <= '0;
            issue0.control.ALUOp    <= '0;
            issue0.control.MemWrite <= '0;
            issue0.control.ALUSrc   <= '0;
            issue0.control.RegWrite <= '0;
        end
        if (issue[1] != 5'b11111) begin // Checks that we found a valid entry
            issue1.valid    <= rsTable[issue[1][3:0]].valid;
            issue1.robNum   <= rsTable[issue[1][3:0]].robNum;
            issue1.pc       <= rsTable[issue[1][3:0]].instruction.pc;
            issue1.rd       <= rsTable[issue[1][3:0]].instruction.rd;
            issue1.rd_old   <= rsTable[issue[1][3:0]].instruction.rd_old;
            issue1.rs1      <= rsTable[issue[1][3:0]].rs1_data;
            issue1.rs2      <= rsTable[issue[1][3:0]].rs2_data;
            issue1.imm      <= rsTable[issue[1][3:0]].instruction.imm;
            issue1.ALUCtrl  <= rsTable[issue[1][3:0]].instruction.ALUCtrl;
            issue1.control  <= rsTable[issue[1][3:0]].instruction.control;
        end else begin
            issue1.valid    <= '0;
            issue1.robNum   <= '0;
            issue1.pc       <= '0;
            issue1.rd       <= '0;
            issue1.rd_old   <= '0;
            issue1.rs1      <= '0;
            issue1.rs2      <= '0;
            issue1.imm      <= '0;
            issue1.ALUCtrl  <= '0;
            issue1.control.MemRead  <= '0;
            issue1.control.MemtoReg <= '0;
            issue1.control.ALUOp    <= '0;
            issue1.control.MemWrite <= '0;
            issue1.control.ALUSrc   <= '0;
            issue1.control.RegWrite <= '0;
        end
        
        if (fuRdy.mem) begin // First check that the FU is ready
            if (issue[2] != 5'b11111) begin // Checks that we found a valid entry
                issue2.valid    <= rsTable[issue[2][3:0]].valid;
                issue2.robNum   <= rsTable[issue[2][3:0]].robNum;
                issue2.pc       <= rsTable[issue[2][3:0]].instruction.pc;
                issue2.rd       <= rsTable[issue[2][3:0]].instruction.rd;
                issue2.rd_old   <= rsTable[issue[2][3:0]].instruction.rd_old;
                issue2.rs1      <= rsTable[issue[2][3:0]].rs1_data;
                issue2.rs2      <= rsTable[issue[2][3:0]].rs2_data;
                issue2.imm      <= rsTable[issue[2][3:0]].instruction.imm;
                issue2.ALUCtrl  <= rsTable[issue[2][3:0]].instruction.ALUCtrl;
                issue2.control  <= rsTable[issue[2][3:0]].instruction.control;
            end 
            // Otherwise, do not issue and hold previous issue in registers
        end
        
        if (fuRdy.mem) begin
            if (issue[2] != 5'b11111) begin // Valid instruction
                fuRdy.mem <= '0; // Not ready
            end
        end else begin
            fuRdy.mem <= '1; // Always 1 unless just used
        end
    end
end

endmodule