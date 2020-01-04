module Filter (CLK,  a, out);
input CLK;
input [7:0] a;
output [7:0] out;
wire [7:0] delay;
wire [7:0] delay1;
wire [23:0] x9;
wire [15:0] x6;
wire [7:0] x;
wire [15:0] x8;
wire [15:0] x7;
wire [7:0] x1;
wire [23:0] next;
wire [7:0] out;
reg [15:0] delay_delay11;

assign delay = delay_delay11[15:8];
assign delay1 = delay_delay11[7:0];
assign x6 = {a, delay };
assign x = x6[7:0];
assign x7 = {x, delay1 };
assign x1 = x7[7:0];
assign x8 = {x7[15:8], ( ( ( x1 + ( x << 1'b1 ) ) + a ) >> 2'b10 ) };
assign x9 = {x8[15:8], {x6[15:8], x8[7:0] } };
assign next = {{x9[15:8], x9[23:16] }, x9[7:0] };
assign out = next[7:0];

initial begin
  delay_delay11 = 16'b0000000000000000;
end

always @ (posedge CLK)
  delay_delay11 <= next[23:8];


endmodule
