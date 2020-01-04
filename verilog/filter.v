module Filter (CLK,  a, out);
input CLK;
input [7:0] a;
output [7:0] out;
wire [7:0] delay;
wire [7:0] delay1;
wire [23:0] x13;
wire [7:0] x3;
wire [15:0] x10;
wire [7:0] x4;
wire [15:0] x12;
wire [15:0] x11;
wire [7:0] x5;
wire [23:0] next;
wire [7:0] out;
reg [15:0] delay_delay11;

assign delay = delay_delay11[15:8];
assign delay1 = delay_delay11[7:0];
assign x3 = a;
assign x10 = {x3, delay };
assign x4 = x10[7:0];
assign x11 = {x4, delay1 };
assign x5 = x11[7:0];
assign x12 = {x11[15:8], ( ( ( x5 + ( x4 << 1'b1 ) ) + x3 ) >> 2'b10 ) };
assign x13 = {x12[15:8], {x10[15:8], x12[7:0] } };
assign next = {{x13[15:8], x13[23:16] }, x13[7:0] };
assign out = next[7:0];

initial begin
  delay_delay11 = 16'b0000000000000000;
end

always @ (posedge CLK)
  delay_delay11 <= next[23:8];


endmodule
