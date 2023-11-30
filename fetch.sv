/*`timescale 1ns/1ps
module fetch(
    input logic clk,
    input logic pc,
    output logic instA,
    output logic instB
);
    reg [31:0] rom [64]; // Assuming 8-bit ROM with variable number of locations
    assign logic line = pc/4;
    initial begin
    // Read data from file into ROM
    $readmemh("data.txt", rom);
    end

    always_ff @(posedge clk) begin
        if(line + 1 < rom.size) begin //both instructions exist
            instA <= rom[line];
            instB <= rom[line+1];
        end else if(line < rom.size) begin //only first one exists
            instA <= rom[line];
            instB <= 32'd0;
        end else begin //we are out of instructions
            instA <= 32'd0;
            instB <= 32'd0;
        end
    end

endmodule */