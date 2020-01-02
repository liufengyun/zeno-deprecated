package ysm

import lang._
import phases._

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
    Bit ~    // read
    Bit ~    // write
    Vec[32]  // write data

  type BusIn =
    Vec[32] // read data

  type ACC   = Vec[32]
  type INSTR = Vec[16]

  def instrMemory(addrWidth: Int, prog: Array[Int], addr: Signal[Vec[addrWidth.type]]): Signal[Vec[16]] = {
    val default: Signal[Vec[16]] = 0.toSignal(16)
    (0 until (1 << addrWidth)).foldLeft(default) { (acc, curAddr) =>
      when[Vec[16]] (addr === curAddr.toSignal(addrWidth)) {
        if (curAddr < prog.size) prog(curAddr).toSignal(16)
        else default
      } otherwise {
        acc
      }
    }
  }

  def stage2(instr: Signal[INSTR], acc: Signal[ACC], busIn: Signal[BusIn]): Signal[ACC] = {
    val opcode  = instr(0, 7).as[Vec[8]]

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

    fsm("processor", pcInit ~ accInit ~ lastInit) { (state: Signal[PC ~ ACC ~ INSTR]) =>
      val pc ~ acc ~ lastInstr = state

      let("pcNext", (pc + 1.toSignal(addrWidth)).as[PC]) { pcNext =>

        let("instr", instrMemory(addrWidth, prog, pc)) { instr =>
          val operand = (0.toSignal(24) ++ instr(8, 15)).as[Vec[32]]
          val opcode  = instr(0, 7).as[Vec[8]]

          val jmpAddr = instr(15 - addrWidth + 1, 15).as[PC]
          val busAddr = instr(8, 15).as[Vec[8]]
          val shiftOperand = instr(12, 15).as[Vec[4]]

          val loadBusOut: Signal[BusOut] = busAddr ~ 1 ~ 0 ~ 0.toSignal(32)

          // forward acc from stage 2
          let("stage2Acc", stage2(lastInstr, acc, busIn)) { acc =>

            def next(
              pc: Signal[PC] = pcNext,
              acc: Signal[ACC] = acc,
              instr: Signal[INSTR] = 0.toSignal(16),
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
              next(pc = jmpAddr)

            } .when (opcode === BRZ.toSignal(8)) {
              when(acc === 0.toSignal(32)) {
                next(pc = jmpAddr)
              }
              .otherwise {
                next()
              }

            } .when (opcode === BRNZ.toSignal(8)) {
              when(acc === 0.toSignal(32)) {
                next()
              }
              .otherwise {
                next(pc = jmpAddr)
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

  def test(file: String): Unit = {
    val busIn = input[BusIn]("busIn")
    val instructions = Assembler.assemble(file)
    val code = processor(instructions, busIn)
    println(count)
    println(show(lift(code)))
  }
}


object Assembler {
  import scala.io.Source
  import ISA._

  def assemble(progPath: String): Array[Int] = {
    // println("parsing file " + progPath)

    val source = Source.fromFile(progPath)

    val lines = source.getLines().toList.map(_.trim).filter { line =>
      !line.isEmpty && !line.startsWith("//")
    }

    // println("effective lines = " + lines.size)
    // println(lines.mkString("\n"))

    val Label = "(.*):".r
    var addr: Int = 0
    val symbols = lines.foldLeft(Map.empty[String, Int]) {
      case (acc, Label(l)) => acc + (l -> addr)
      case (acc, _)        => addr += 1; acc
    }

    // println("labels: " + symbols)

    def toInt(s: String): Int = {
      // TODO: check valid range of the argument
      if (s.startsWith("0x")) {
        Integer.parseInt(s.substring(2), 16)
      } else {
        Integer.parseInt(s)
      }
    }

    def address(s: String): Int = {
      s.toInt
    }

    // println("lines size = " + lines.size)

    val instructions = for (line <- lines if !line.matches("(.*:)")) yield {
      val tokens = line.split("\\s+")
      tokens(0) match {
        case "nop"     => NOP
        case "add"     => (ADD    << 8) + address(tokens(1))
        case "sub"     => (SUB    << 8) + address(tokens(1))
        case "and"     => (AND    << 8) + address(tokens(1))
        case "or"      => (OR     << 8) + address(tokens(1))
        case "xor"     => (XOR    << 8) + address(tokens(1))
        case "addi"    => (ADDI   << 8) + toInt(tokens(1))
        case "subi"    => (SUBI   << 8) + toInt(tokens(1))
        case "andi"    => (ANDI   << 8) + toInt(tokens(1))
        case "ori"     => (ORI    << 8) + toInt(tokens(1))
        case "xori"    => (XORI   << 8) + toInt(tokens(1))
        case "shr"     => (SHR    << 8) + toInt(tokens(1))
        case "shl"     => (SHL    << 8) + toInt(tokens(1))
        case "load"    => (LD     << 8) + address(tokens(1))
        case "loadi"   => (LDI    << 8) + toInt(tokens(1))
        case "store"   => (ST     << 8) + address(tokens(1))
        case "br"      => (BR     << 8) + symbols(tokens(1))
        case "brz"     => (BRZ    << 8) + symbols(tokens(1))
        case "brnz"    => (BRNZ   << 8) + symbols(tokens(1))
        case t: String => throw new Exception("Assembler error: unknown instruction: " + t)
      }
    }

    // println("instr size: " + instructions.size)

    instructions.toArray
  }
}
