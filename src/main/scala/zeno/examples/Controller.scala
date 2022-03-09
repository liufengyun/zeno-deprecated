package zeno.examples.controller

import zeno.lang._
import zeno.core.Values

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
   val EXIT    =    0x13
}

object Controller {
  import ISA._

  type Debug =
    Vec[32] ~ // acc
    Vec[_] ~ // pc
    Vec[16] ~ // instr
    Bit       // exit

  type BusOut =
    Vec[8] ~ // addr
    Bit ~    // read
    Bit ~    // write
    Vec[32]  // write data

  type BusIn =
    Vec[32] // read data

  final val InstrAddrSize: Int = 6

  type ACC   = Vec[32]
  type INSTR = Vec[16]
  type PC    = Vec[InstrAddrSize.type]

  def instrMemory(prog: Array[Int], addr: Sig[Vec[InstrAddrSize.type]]): Sig[Vec[16]] = {
    def recur(acc: Int, bitIndex: Int): Sig[Vec[16]] =
      if bitIndex >= InstrAddrSize then
        if acc >= prog.length then 0.W[16]
        else prog(acc).W[16]
      else
        when (addr(bitIndex)) { recur((1 << bitIndex) + acc, bitIndex + 1) }
        .otherwise { recur(acc, bitIndex + 1) }
    recur(0, 0)
  }

  def processor(prog: Array[Int], busIn: Sig[BusIn]): Sig[BusOut ~ Debug] = {
    assert(prog.size < (1 << 12))

    val pc0: Value   = 0.toValue(InstrAddrSize)
    val acc0: Value  = 0.toValue(32)
    val mode0: Value = 0.toValue(1)

    val defaultBusOut: Sig[BusOut] = 0.W[8] ~ 0 ~ 0 ~ 0.W[32]

    fsm("processor", pc0 ~ acc0 ~ mode0) { (state: Sig[PC ~ ACC ~ Bit]) =>
      val pc ~ acc ~ mode = state

      let("pcNext", pc + 1.W[InstrAddrSize.type]) { pcNext =>

        let("instr", instrMemory(prog, pc)) { instr =>
          val operand = (0.W[24] ++ instr(7, 0)).as[Vec[32]]
          val opcode  = instr(15, 8).as[Vec[8]]

          def next(
            pc: Sig[PC] = pcNext,
            acc: Sig[ACC] = acc,
            mode: Sig[Bit] = 0,
            out: Sig[BusOut] = defaultBusOut,
            exit: Boolean = false
          ): Sig[(PC ~ ACC ~ Bit) ~ (BusOut ~ Debug)] = {
            val debug = acc ~ (pc.as[Vec[_]]) ~ instr ~ exit
            (pc ~ acc ~ mode) ~ (out ~ debug)
          }

          when (mode) {
            // pending mode
            val opcode  = instr(15, 8).as[Vec[8]]

            when (opcode === ADD.W[8]) {
              next(acc = acc + busIn)
            } .when (opcode === SUB.W[8]) {
              next(acc = acc - busIn)
            } .when (opcode === LD.W[8]) {
              next(acc = busIn)
            } .when (opcode === AND.W[8]) {
              next(acc = acc & busIn)
            } .when (opcode === OR.W[8]) {
              next(acc = acc | busIn)
            } .when (opcode === XOR.W[8]) {
              next(acc = acc ^ busIn)
            } .otherwise {
              next()
            }
          } otherwise {
            val jmpAddr = instr(InstrAddrSize - 1, 0).as[PC]
            val busAddr = instr(7, 0).as[Vec[8]]
            val shiftOperand = instr(3, 0).as[Vec[4]]

            val loadBusOut: Sig[BusOut] = busAddr ~ 1 ~ 0 ~ 0.W[32]

            when (opcode === ADDI.W[8]) {
              val acc2 = acc + operand
              next(acc = acc2)

            } .when (opcode === SUBI.W[8]) {
              val acc2 = acc - operand
              next(acc = acc2)

            } .when (opcode === LDI.W[8]) {
              next(acc = operand)

            } .when (opcode === ST.W[8]) {
              val busOut: Sig[BusOut] = busAddr ~ 0 ~ 1 ~ acc
              next(out = busOut)

            } .when (opcode === ANDI.W[8]) {
              val acc2 = acc & operand
              next(acc = acc2)

            } .when (opcode === ORI.W[8]) {
              val acc2 = acc | operand
              next(acc = acc2)

            } .when (opcode === XORI.W[8]) {
              val acc2 = acc ^ operand
              next(acc = acc2)

            } .when (opcode === SHL.W[8]) {
              val acc2 = acc << shiftOperand
              next(acc = acc2)

            } .when (opcode === SHR.W[8]) {
              val acc2 = acc >> shiftOperand
              next(acc = acc2)

            } .when (opcode === BR.W[8]) {
              next(pc = jmpAddr)

            } .when (opcode === BRZ.W[8]) {
              when(acc === 0.W[32]) {
                next(pc = jmpAddr)
              }
              .otherwise {
                next()
              }

            } .when (opcode === BRNZ.W[8]) {
              when(acc === 0.W[32]) {
                next()
              }
              .otherwise {
                next(pc = jmpAddr)
              }

            } .when (opcode === ADD.W[8]) {
              next(pc = pc, out = loadBusOut, mode = 1)

            } .when (opcode === SUB.W[8]) {
              next(pc = pc, out = loadBusOut, mode = 1)

            } .when (opcode === LD.W[8]) {
              next(pc = pc, out = loadBusOut, mode = 1)

            } .when (opcode === AND.W[8]) {
              next(pc = pc, out = loadBusOut, mode = 1)

            } .when (opcode === OR.W[8]) {
              next(pc = pc, out = loadBusOut, mode = 1)

            } .when (opcode === XOR.W[8]) {
              next(pc = pc, out = loadBusOut, mode = 1)

            } .when (opcode === EXIT.W[8]) {
              next(exit = true)

            } .otherwise { // NOP
              next()

            }
          }
        }
      }
    }
  }

  def test(prog: String): String = {
    val busIn = input[BusIn]("busIn")
    val instructions = Assembler.assemble(prog)
    val code = processor(instructions, busIn)
    // println(show(code))
    val fsm = code.eval(busIn)

    var run = true
    var maxInstructions = 30000
    val sb = new StringBuilder

    val memory = scala.collection.mutable.Map.empty[Short, Int]

    var inputV: Value = 0.toValue(32)
    while(run) {
      val (addr ~ read ~ write ~ writedata) ~ (acc ~ pc ~ instr ~ exit) = fsm(inputV :: Nil)

      if (write.toInt == 1) {
        val data = writedata.toInt
        if (addr.toShort == 0) {
          val char = data.toChar
          sb.append(char)
        }
        else {
          memory(addr.toShort) = data
        }
      }

      if (read.toInt == 1) {
        val data = memory.getOrElse(addr.toShort, 0)
        inputV = data.toValue(32)
      }

      // println("pc = " + pc.toInt)
      // println("acc = " + acc.toInt)

      // displayPrompt()

      maxInstructions -= 1
      run = exit.toInt == 0 && maxInstructions > 0
    }

    sb.toString
  }

  def testDetupled(prog: String): String = {
    import zeno.rewrite.Phases

    val busIn = input[BusIn]("busIn")
    val instructions = Assembler.assemble(prog)
    val code = processor(instructions, busIn)
    val detupled = Phases.detuple(code)
    // println(show(detupled))
    val fsm = detupled.eval(busIn)

    var run = true
    var maxInstructions = 30000
    val sb = new StringBuilder

    val memory = scala.collection.mutable.Map.empty[Short, Int]

    var inputV: Value = 0.toValue(32)
    while(run) {
      val output = fsm(inputV :: Nil).asInstanceOf[Values.VecV]
      val hi = output.width - 1
      val addr = output(hi, hi - 7)
      val read = output(hi - 8)
      val write = output(hi - 9)
      val writedata = output(hi - 10, hi - 10 - 31)
      val exit = output(0)

      // println("width = " + output.width)
      // println("write = " + write.toInt)
      // println("writedata = " + writedata.toInt)

      if (write.toInt == 1) {
        val data = writedata.toInt
        if (addr.toShort == 0) {
          val char = data.toChar
          sb.append(char)
        }
        else {
          memory(addr.toShort) = data
        }
      }

      if (read.toInt == 1) {
        val data = memory.getOrElse(addr.toShort, 0)
        inputV = data.toValue(32)
      }

      // println("pc = " + pc.asInstanceOf[Value[Vec[0]]].toInt)
      // println("acc = " + acc.toInt)

      // displayPrompt()

      maxInstructions -= 1
      run = exit.toInt == 0 && maxInstructions > 0
    }

    sb.toString
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

    // println("effective lines = " + lines.width)
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

    // println("lines width = " + lines.width)

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
        case "exit"    => (EXIT   << 8)
        case t: String => throw new Exception("Assembler error: unknown instruction: " + t)
      }
    }

    // println("instr width: " + instructions.width)

    instructions.toArray
  }
}
