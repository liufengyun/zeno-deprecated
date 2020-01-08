package nand
package rewrite

import nand.lang._

import core._
import Types._, Trees._, Values._

import Phases._

object Verilog {
  def emit[T <: Type](moduleName: String, input: List[Var[_]], sig: Signal[T]): String = {
    val normailized = inlining(detuple(inlining(anf(flatten(lift(sig))))))

    import scala.collection.mutable.ListBuffer

    val wires: ListBuffer[String] = ListBuffer.empty
    val assigns: ListBuffer[String] = ListBuffer.empty
    val regs: ListBuffer[String] = ListBuffer.empty

    def template(body: String, sequential: Boolean = false): String = {
      val inputNames = input.map(_.name).mkString(", ")
      val inputDecls = input.map { variable =>
        val hi = detuple(variable).width -  1
        s"input [$hi:0] ${variable.name};"
      }.mkString("\n")

      val outDecl = {
        val hi = normailized.width - 1
        wires += s"wire [$hi:0] out;"
        s"output [$hi:0] out;"
      }

      val clockPort = if (sequential) "CLK, " else ""
      val clockDecl = if (sequential) "input CLK;\n" else ""

      s"module $moduleName ($clockPort $inputNames, out);\n" +
      clockDecl +
      s"$inputDecls\n" +
      s"$outDecl\n" +
      wires.mkString("\n") + "\n" +
      regs.mkString("\n") + "\n\n" +
      assigns.mkString("\n") + "\n\n" +
      s"$body\n" +
      "endmodule\n"
    }

    def letHandler(let: Let[_, _]): String = {
      val name = let.sym.name
      val hi = let.sig.width - 1
      wires += s"wire [$hi:0] $name;"

      val rhs = recur(let.sig)
      assigns += s"assign $name = $rhs;"

      recur(let.body)
    }

    def bits2Verilog(bits: List[Int]): String = {
      val bin = bits.map(_.toString).mkString
      val s = bits.size
      s"$s'b$bin"
    }

    def recur[T <: Type](sig: Signal[T]): String = { /* println(show(sig)); */ sig} match {
      case At(vec, index)         =>
        val vec1 = recur(vec)
        s"$vec1[$index]"

      case Range(vec, to, from)   =>
        val vec1 = recur(vec)
        s"$vec1[$to:$from]"

      case VecLit(bits)           =>
        bits2Verilog(bits)

      case Var(sym, tpe)          =>
        sym.name

      case let @ Let(_, _, _)    =>
        letHandler(let)

      case And(lhs, rhs)          =>
        "( " + recur(lhs) + " & " + recur(rhs) + " )"

      case Or(lhs, rhs)           =>
        "( " + recur(lhs) + " | " + recur(rhs) + " )"

      case Not(in)                =>
        "~" + recur(in)

      case Concat(lhs, rhs)     =>
        "{" + recur(lhs) + ", " + recur(rhs) + " }"

      case Equals(lhs, rhs)     =>
        "( " + recur(lhs) + " == " + recur(rhs) + " )"

      case Plus(lhs, rhs)       =>
        "( " + recur(lhs) + " + " + recur(rhs) + " )"

      case Minus(lhs, rhs)      =>
        "( " + recur(lhs) + " - " + recur(rhs) + " )"

      case Mux(cond, thenp, elsep)  =>
        "( " + recur(cond) + "? " + recur(thenp) + " : " + recur(elsep) + " )"

      case Shift(lhs, rhs, isLeft)   =>
        val op = if (isLeft) "<<" else ">>"

        "( " + recur(lhs) + s" $op " + recur(rhs) + " )"

      case Par(_, _) | Left(_) | Right(_) =>
        ??? // impossible after detupling

      case Fsm(_, _, _)   =>
        ??? // impossible after flattening
    }


    normailized match {
      case fsm @ Fsm(sym, init, body) =>
        val hi = body.width - 1
        val lo = fsm.width
        val hiOut = lo - 1

        val stateHi = body.width - fsm.width - 1
        regs += s"reg [$stateHi:0] ${sym.name};"

        val initial = {
          val bin = bits2Verilog(init.asInstanceOf[VecV].bits)
          s"""|initial begin
              |  ${sym.name} = $bin;
              |end\n\n""".stripMargin
        }

        body match {
          case Concat(sigState, sigOut) => // no need to generate next, save wire bits
            val state = recur(sigState)
            val out = recur(sigOut)
            assigns += s"assign out = $out;"

            val always = {
              s"""|always @ (posedge CLK)
                  |  ${sym.name} <= $state;\n\n""".stripMargin
            }

            template(initial + always, sequential = true)

          case _ =>
            val next = recur(body)
            wires += s"wire [$hi:0] next;"
            assigns += s"assign next = $next;"
            assigns += s"assign out = next[$hiOut:0];"

            val always = {
              s"""|always @ (posedge CLK)
                  |  ${sym.name} <= next[$hi:$lo];\n\n""".stripMargin
            }

            template(initial + always, sequential = true)
        }

      case code => // combinational
        val out = recur(code)
        assigns += s"assign out = $out;"
        template("")
    }
  }
}