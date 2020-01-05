module Filter (CLK,  a, out);
input CLK;
input [7:0] a;
output [7:0] out;
wire [7:0] x843;
wire [23:0] next;
wire [7:0] out;
reg [15:0] delay_delay12;

assign x843 = ( ( ( delay_delay12[7:0] + ( delay_delay12[15:8] << 1'b1 ) ) + a ) >> 2'b10 );
assign next = {{a, delay_delay12[15:8] }, x843 };
assign out = next[7:0];

initial begin
  delay_delay12 = 16'b0000000000000000;
end

always @ (posedge CLK)
  delay_delay12 <= next[23:8];


endmodule
