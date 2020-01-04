module MovingAverage3( // @[:@3.2]
  input        clock, // @[:@4.4]
  input        reset, // @[:@5.4]
  input  [7:0] io_in, // @[:@6.4]
  output [7:0] io_out // @[:@6.4]
);
  reg [7:0] z1; // @[Chisel.scala 10:19:@8.4]
  reg [31:0] _RAND_0;
  reg [7:0] z2; // @[Chisel.scala 11:19:@10.4]
  reg [31:0] _RAND_1;
  wire [8:0] _GEN_0; // @[Chisel.scala 13:26:@12.4]
  wire [8:0] _T_12; // @[Chisel.scala 13:26:@12.4]
  wire [8:0] _GEN_1; // @[Chisel.scala 13:20:@13.4]
  wire [9:0] _T_13; // @[Chisel.scala 13:20:@13.4]
  wire [8:0] _T_14; // @[Chisel.scala 13:20:@14.4]
  wire [8:0] _GEN_2; // @[Chisel.scala 13:34:@15.4]
  wire [9:0] _T_15; // @[Chisel.scala 13:34:@15.4]
  wire [8:0] _T_16; // @[Chisel.scala 13:34:@16.4]
  wire [8:0] _T_18; // @[Chisel.scala 13:40:@17.4]
  assign _GEN_0 = {{1'd0}, z1}; // @[Chisel.scala 13:26:@12.4]
  assign _T_12 = _GEN_0 << 1'h1; // @[Chisel.scala 13:26:@12.4]
  assign _GEN_1 = {{1'd0}, io_in}; // @[Chisel.scala 13:20:@13.4]
  assign _T_13 = _GEN_1 + _T_12; // @[Chisel.scala 13:20:@13.4]
  assign _T_14 = _GEN_1 + _T_12; // @[Chisel.scala 13:20:@14.4]
  assign _GEN_2 = {{1'd0}, z2}; // @[Chisel.scala 13:34:@15.4]
  assign _T_15 = _T_14 + _GEN_2; // @[Chisel.scala 13:34:@15.4]
  assign _T_16 = _T_14 + _GEN_2; // @[Chisel.scala 13:34:@16.4]
  assign _T_18 = _T_16 >> 2'h2; // @[Chisel.scala 13:40:@17.4]
  assign io_out = _T_18[7:0]; // @[Chisel.scala 13:10:@18.4]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE
  integer initvar;
  initial begin
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      #0.002 begin end
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  z1 = _RAND_0[7:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  z2 = _RAND_1[7:0];
  `endif // RANDOMIZE_REG_INIT
  end
`endif // RANDOMIZE
  always @(posedge clock) begin
    z1 <= io_in;
    z2 <= z1;
  end
endmodule
