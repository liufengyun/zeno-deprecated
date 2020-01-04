## Ysm

Yet another State Machine

`sbt > run asm/hello.s`

### Tests

```
sbt test
```

### Verilog

First install [Yosys](https://github.com/YosysHQ/yosys):

```
brew install yosys
```

To check the synthesized result:

```
yosys -S verilog/filter.v
```

With FPGA as target:

```
yosys -p synth_xilinx -S verilog/adder.v
```
