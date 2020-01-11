package zeno
package util

import core._
import Types._, Trees._, Values._

object Printing {
  def show[T <: Type](sig: Signal[T]): String = {
    var indent = 0

    def padding: String = "\n" + ("  " * indent)

    def indented(str: => String): String = indentedWith(tabs = 1)(str)

    def indentedWith(tabs: Int)(str: => String): String = {
      indent += 1
      val res = str
      indent -= 1
      res
    }

    def inParens(content: String): String = "(" + content + ")"

    def recur[T <: Type](sig: Signal[T]): String =
      sig match {
        case Pair(lhs, rhs) => recur(lhs) + " ~ " + recur(rhs)

        case Left(pair)    => recur(pair) + ".1"

        case Right(pair)   => recur(pair) + ".2"

        case At(vec, i)    => recur(vec) + "[" + i + "]"

        case Range(vec, to, from) =>
          recur(vec) + "[" + to + ".." + from + "]"

        case VecLit(Nil)   =>
          "Vec()"

        case VecLit(bits)   =>
          if (bits.size <= 4) bits.map(_.toString).mkString
          else toHex(bits)

        case Concat(vec1, vec2) =>
          inParens { recur(vec1) + " ++ " + recur(vec2) }

        case Var(sym, tpe)  =>
          sym.name

        case Let(sym, sig, body) =>
          indented {
            padding + "let " + sym.name + ": " + show(sig.tpe)  +  " = " + recur(sig) +
            padding + "in" +
            padding + indented { recur(body) }
          }

        case Fsm(sym, init, body) =>
          indented {
            padding + "fsm { " + show(init) + " | " + sym.name + " => " +
            indentedWith(tabs = 2) { padding + recur(body) } +
            padding + "}"
          }

        case Equals(vec1, vec2) =>
          recur(vec1) + "===" + recur(vec2)

        case Plus(vec1, vec2) =>
          inParens { recur(vec1) + " + " + recur(vec2) }

        case Minus(vec1, vec2) =>
          inParens { recur(vec1) + " - " + recur(vec2) }

        case Shift(vec, amount, isLeft) =>
          val dir = if (isLeft) " << " else " >> "
          inParens { recur(vec) + dir + recur(amount) }

        case Mux(cond, vec1, vec2) =>
          indented {
            padding + "if (" + recur(cond) + ") " + recur(vec1) +
            padding + "else " + recur(vec2)
          }

        case And(lhs, rhs)  =>
          inParens {  recur(lhs) + " & " + recur(rhs) }

        case Or(lhs, rhs)   =>
          inParens { recur(lhs) + " | " + recur(rhs) }

        case Not(in)        =>
          "!" + recur(in)
      }

    recur(sig)
  }

  def show(tpe: Type): String = tpe match {
    case PairT(t1, t2) => show(t1) + " ~ " + show(t2)
    case VecT(width)    => "Vec[" + width + "]"
  }

  def show(value: Value): String = value match {
    case PairV(l, r)     => show(l) + " ~ " + show(r)
    case VecV(bits)      =>
      if (bits.size <= 4) bits.map(_.toString).mkString else toHex(bits)
  }

  def toHex(bits: List[0 | 1]): String = {
    var base: Int = 1
    var sum: Int = 0
    var count: Int = 0
    val sb = new StringBuilder
    bits.foldRight(sb) { (bit, sbt) =>
      count += 1
      sum += bit * base
      base *= 2

      if (base > 8 || count == bits.size) {
        base = 1

        if(sum < 10) sb.insert(0, sum.toString)
        else if(sum == 10) sb.insert(0, "A")
        else if(sum == 11) sb.insert(0, "B")
        else if(sum == 12) sb.insert(0, "C")
        else if(sum == 13) sb.insert(0, "D")
        else if(sum == 14) sb.insert(0, "E")
        else if(sum == 15) sb.insert(0, "F")

        sum = 0
      }

      sb
    }

    sb.toString
  }
}