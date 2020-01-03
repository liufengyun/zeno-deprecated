module Shift ( a, b, out);
input [7:0] a;
input [3:0] b;
output [7:0] out;
wire out;


assign out = ( a << b );


endmodule
