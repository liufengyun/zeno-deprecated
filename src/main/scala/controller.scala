package ysm

import lang._

import scala.language.implicitConversions

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
  import ISA._

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

  type ACC = Vec[32]
  type INSTR = Vec[16]

  def instrMemory(addrWidth: Int, prog: Array[Int], addr: Signal[Vec[addrWidth.type]]): Signal[Vec[16]] = {
    val default: Signal[Vec[16]] = 0.toSignal(16)
    (0 until (1 << addrWidth)).foldLeft(default) { (acc, curAddr) =>
      when[Vec[16]] (addr === curAddr.toSignal(addrWidth)) {
        prog(curAddr).toSignal(16)
      } otherwise {
        acc
      }
    }
  }

  def stage2(instr: Signal[Vec[INSTR]], acc: Signal[ACC], busIn: Signal[BusIn]): Signal[ACC] = {
    val opcode  = instr.range(0, 7).as[Vec[8]]

    when (opcode === ADD.toSignal(8)) {
      (acc + busIn).as[ACC]
    } .when (opcode === SUB.toSignal(8)) {
      (acc - busIn).as[ACC]
    } .when (opcode === LD.toSignal(8)) {
      busIn
    } .when (opcode === AND.toSignal(8)) {
      acc & busIn
    } .when (opcode === OR.toSignal(8)) {
      acc | busIn
    } .when (opcode === XOR.toSignal(8)) {
      acc ^ busIn
    } .otherwise {
      acc
    }
  }

  def processor(prog: Array[Int], busIn: Signal[BusIn]): Signal[BusOut] = {
    assert(prog.size > 0)
    var addrW = 1
    while ((1 << addrW) < prog.size) addrW+=1

    val addrWidth = addrW
    type PC  = Vec[addrWidth.type]

    val pcInit: Value[PC]      = 0.toValue(addrWidth)
    val accInit: Value[ACC]    = 0.toValue(32)
    val lastInit: Value[INSTR] = 0.toValue(16)

    val defaultBusOut: Signal[BusOut] = 0.toSignal(8) ~ 0 ~ 0 ~ 0.toSignal(32)

    fsm("processor", pcInit ~ accInit ~ lastInit) { (s: Signal[PC ~ ACC ~ INSTR]) =>
      let("pcNext", (s.left + 1.toSignal(addrWidth)).as[PC]) { pcNext =>
        val acc = s.right

        let("instr", instrMemory(addrWidth, prog, s.left)) { instr =>
          val operand = (0.toSignal(24) ++ instr.range(8, 15)).as[Vec[32]]
          val opcode  = instr.range(0, 7).as[Vec[8]]

          val instrAddr = instr.range(15 - addrWidth - 1, 15).as[PC]
          val busAddr = instr.range(8, 15).as[Vec[8]]
          val shiftOperand = instr.range(12, 15).as[Vec[4]]

          val loadBusOut: Signal[BusOut] = busAddr ~ 1 ~ 0 ~ 0.toSignal(32)

          // forward acc from stage 2
          let("stage2Acc", stage2(s.right.right, acc, busIn)) { acc =>

            def next(
              pc: Signal[PC] = pcNext,
              acc: Signal[ACC] = acc,
              instr: Signal[INSTR] = 0.toSignal(32),
              out: Signal[BusOut] = defaultBusOut
            ): Signal[(PC ~ ACC ~ INSTR) ~ BusOut] = (pc ~ acc ~ instr) ~ out

            when (opcode === ADDI.toSignal(8)) {
              val acc2 = (acc + operand).as[ACC]
              next(acc = acc2)

            } .when (opcode === SUBI.toSignal(8)) {
              val acc2 = (acc - operand).as[ACC]
              next(acc = acc2)

            } .when (opcode === LDI.toSignal(8)) {
              next(acc = operand)

            } .when (opcode === ST.toSignal(8)) {
              val busOut: Signal[BusOut] = busAddr ~ 0 ~ 1 ~ acc
              next(out = busOut)

            } .when (opcode === ANDI.toSignal(8)) {
              val acc2 = acc & operand
              next(acc = acc2)

            } .when (opcode === ORI.toSignal(8)) {
              val acc2 = acc | operand
              next(acc = acc2)

            } .when (opcode === XORI.toSignal(8)) {
              val acc2 = acc ^ operand
              next(acc = acc2)

            } .when (opcode === SHL.toSignal(8)) {
              val acc2 = (acc << shiftOperand).as[ACC]
              next(acc = acc2)

            } .when (opcode === SHR.toSignal(8)) {
              val acc2 = (acc >> shiftOperand).as[ACC]
              next(acc = acc2)

            } .when (opcode === BR.toSignal(8)) {
              next(pc = instrAddr)

            } .when (opcode === BRZ.toSignal(8)) {
              when(acc === 0.toSignal(32)) {
                next(pc = instrAddr)
              }
              .otherwise {
                next()
              }

            } .when (opcode === BRNZ.toSignal(8)) {
              when(acc === 0.toSignal(32)) {
                next()
              }
              .otherwise {
                next(pc = instrAddr)
              }

            } .when (opcode === ADD.toSignal(8)) {
              next(out = loadBusOut, instr = instr)

            } .when (opcode === SUB.toSignal(8)) {
              next(out = loadBusOut, instr = instr)

            } .when (opcode === LD.toSignal(8)) {
              next(out = loadBusOut, instr = instr)

            } .when (opcode === AND.toSignal(8)) {
              next(out = loadBusOut, instr = instr)

            } .when (opcode === OR.toSignal(8)) {
              next(out = loadBusOut, instr = instr)

            } .when (opcode === XOR.toSignal(8)) {
              next(out = loadBusOut, instr = instr)

            } .otherwise { // NOP
              next()

            }
          }
        }
      }
    }
  }
}