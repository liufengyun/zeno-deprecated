package ysm

import lang._


 object ISA {
   val NOP     =    0x00
   val ADD     =    0x01
   val ADDI    =    0x02
   val SUB     =    0x03
   val SUBI    =    0x04
   val SHL     =    0x05
   val SHR     =    0x06
   val LD      =    0x07
   val LDI     =    0x08
   val ST      =    0x09
   val AND     =    0x0a
   val ANDI    =    0x0b
   val OR      =    0x0c
   val ORI     =    0x0d
   val XOR     =    0x0e
   val XORI    =    0x0f
   val BR      =    0x10
   val BRZ     =    0x11
   val BRNZ    =    0x12
}

object Controller {
  type Debug =
    Vec[32] ~ // acc
    Vec[32] ~ // pc
    Vec[32] ~ // instr
    Vec[32]   // exit

  type BusOut =
    Vec[8] ~ // addr
    Vec[1] ~ // read
    Vec[1] ~ // write
    Vec[32]  // write data

  type BusIn =
    Vec[32] // read data

  def instrMemory(addrWidth: Int, prog: Array[Int], addr: Signal[Vec[addrWidth.type]]): Signal[Vec[16]] = {
    val default: Signal[Vec[16]] = 0.toSignal(16)
    (0 until (1 << addrWidth)).foldLeft(default) { (acc, curAddr) =>
      when (addr === curAddr.toSignal(addrWidth))(prog(curAddr).toSignal(16), acc)
    }
  }

  def processor(prog: Array[Int], busIn: Signal[BusIn]): Signal[BusOut] = {
    assert(prog.size > 0)
    var addrW = 1
    while ((1 << addrW) < prog.size) addrW+=1

    val addrWidth = addrW
    type PC  = Vec[addrWidth.type]
    type ACC = Vec[32]

    val pcInit: PC   = 0.toVec(addrWidth)
    val accInit: ACC = 0.toVec(32)

    fsm("processor", pcInit ~ accInit) { (s: Signal[PC ~ ACC]) =>
      ???
    }
  }
}