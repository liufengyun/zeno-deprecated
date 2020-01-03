module Adder ( a, b, out);
input [1:0] a;
input [1:0] b;
output [2:0] out;
wire [1:0] x2;
wire [1:0] x;
wire [1:0] x1;
wire [1:0] x5;
wire [1:0] x3;
wire [1:0] x4;
wire out;


assign x = {( a[0] & b[0] ), ( ( a[0] & ~b[0] ) | ( ~a[0] & b[0] ) ) };
assign x1 = {( x[0] & 1'b0 ), ( ( x[0] & ~1'b0 ) | ( ~x[0] & 1'b0 ) ) };
assign x2 = {( x[1] | x1[1] ), x1[0] };
assign x3 = {( a[1] & b[1] ), ( ( a[1] & ~b[1] ) | ( ~a[1] & b[1] ) ) };
assign x4 = {( x3[0] & x2[1] ), ( ( x3[0] & ~x2[1] ) | ( ~x3[0] & x2[1] ) ) };
assign x5 = {( x3[1] | x4[1] ), x4[0] };
assign out = {{x5[1], x5[0] }, x2[0] };


endmodule
