module Filter (CLK,  a, out);
input CLK;
input [7:0] a;
output [7:0] out;
wire [7:0] out;
reg [15:0] s_s12;

assign out = ( ( ( s_s12[7:0] + ( s_s12[15:8] << 1'b1 ) ) + a ) >> 2'b10 );

initial begin
  s_s12 = 16'b0000000000000000;
end

always @ (posedge CLK)
  s_s12 <= {a, s_s12[15:8] };


endmodule
