module Filter ( a, out);
input [7:0] a;
output [7:0] out;
wire [7:0] delay;
wire [7:0] delay1;
wire [23:0] x19;
wire [7:0] x9;
wire [15:0] x16;
wire [7:0] x10;
wire [15:0] x18;
wire [15:0] x17;
wire [7:0] x11;
wire [23:0] next;
wire out;
reg [15:0] state;

assign delay = delay_delay11[15:8];
assign delay1 = delay_delay11[7:0];
assign x9 = a;
assign x16 = {x9, delay };
assign x10 = x16[7:0];
assign x17 = {x10, delay1 };
assign x11 = x17[7:0];
assign x18 = {x17[15:8], ( ( ( x11 + ( x10 << 1'b1 ) ) + x9 ) >> 2'b10 ) };
assign x19 = {x18[15:8], {x16[15:8], x18[7:0] } };
assign next = {{x19[15:8], x19[23:16] }, x19[7:0] };
assign out = next[7:0];

initial begin
  state = 16'b0000000000000000;
end

always @ (posedge CLK)
  state <= next[23:8]


endmodule
