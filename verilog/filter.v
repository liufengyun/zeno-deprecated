module Filter (CLK,  a, out);
input CLK;
input [7:0] a;
output [7:0] out;
wire [7:0] delay;
wire [7:0] delay1;
wire [23:0] x17;
wire [15:0] x14;
wire [7:0] x;
wire [15:0] x16;
wire [15:0] x15;
wire [7:0] x1;
wire [23:0] next;
wire [7:0] out;
reg [15:0] delay_delay12;

assign delay = delay_delay12[15:8];
assign delay1 = delay_delay12[7:0];
assign x14 = {a, delay };
assign x = x14[7:0];
assign x15 = {x, delay1 };
assign x1 = x15[7:0];
assign x16 = {x15[15:8], ( ( ( x1 + ( x << 1'b1 ) ) + a ) >> 2'b10 ) };
assign x17 = {x16[15:8], {x14[15:8], x16[7:0] } };
assign next = {{x17[15:8], x17[23:16] }, x17[7:0] };
assign out = next[7:0];

initial begin
  delay_delay12 = 16'b0000000000000000;
end

always @ (posedge CLK)
  delay_delay12 <= next[23:8];


endmodule
