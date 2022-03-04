package zeno
package rewrite

import lang._

import core._
import Types._, Trees._, Values._

object Interpreter {
  def eval[T <: Type](input: List[Var[_]], body: Sig[T]): List[Value] => Value = {
    def and(lhs: Value, rhs: Value): Value = (lhs, rhs) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        (and(lhs1, lhs2) ~ and(rhs1, rhs2))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        VecV(bits1.zip(bits2).map { case (a, b) => a & b }.asInstanceOf[List[0 | 1]])

      case _ => ??? // impossible
    }

    def or(lhs: Value, rhs: Value): Value = (lhs, rhs) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        (or(lhs1, lhs2) ~ or(rhs1, rhs2))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        VecV(bits1.zip(bits2).map { case (a, b) => a | b }.asInstanceOf[List[0 | 1]])

      case _ => ??? // impossible
    }

    def not(in: Value): Value = (in: @unchecked) match {
      case lhs ~ rhs =>
        (not(lhs) ~ not(rhs))

      case VecV(bits) =>
        VecV(bits.map(i => (i - 1).asInstanceOf[0 | 1]))
    }

    def equals(lhs: Value, rhs: Value): Value = ((lhs, rhs): @unchecked) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        and(equals(lhs1, lhs2), equals(rhs1, rhs2))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        (0 until bits1.size).foldLeft(Value(1)) { (acc, i) =>
          if (bits1(i) == bits2(i)) acc else Value(0)
        }

      // case _ => ??? // impossible
    }

    def plus(lhs: VecV, rhs: VecV): VecV = {
      val width = lhs.width

      assert(lhs.width == rhs.width, "lhs.width = " + lhs.width + ", rhs.width = " + rhs.width)

      val (bits, cout) = (0 until width).foldLeft((Nil, 0): (List[Int], Int)) { case ((bits, cin), i) =>
        val a = lhs(i)
        val b = rhs(i)
        val s = a ^ b ^ cin
        val cout = (a & b) | (cin & (a ^ b))
        (s :: bits, cout)
      }

      VecV(bits.asInstanceOf[List[1 | 0]])
    }

    def minus(lhs: VecV, rhs: VecV): VecV = {
      val width = lhs.width

      assert(lhs.width == rhs.width, "lhs.width = " + lhs.width + ", rhs.width = " + rhs.width)

      val (bits, bout) = (0 until width).foldLeft((Nil, 0): (List[Int], Int)) { case ((bits, bin), i) =>
        val a = lhs(i)
        val b = rhs(i)
        val d = a ^ b ^ bin
        val bout = ((1 - a) & b) | ((1 - a) & bin) | (b & bin)
        (d :: bits, bout)
      }

      VecV(bits.asInstanceOf[List[1 | 0]])
    }

    def shift(lhs: VecV, rhs: VecV, isLeft: Boolean): VecV = {
      val bits: List[Int] = lhs.bits
      val res = (0 until rhs.width).foldLeft(bits) { (acc, i) =>
        val bitsToShift = 1 << i
        val padding = (0 until bitsToShift).map(_ => 0).toList
        val shifted =
          if (isLeft) acc.drop(bitsToShift) ++ padding
          else padding ++ acc.dropRight(bitsToShift)

        if (rhs(i) == 1) shifted
        else acc
      }

      VecV(res.asInstanceOf[List[0 | 1]])
    }

    def recur[T <: Type](sig: Sig[T])(implicit env: Map[Symbol, Value]): Value = { /* println(show(sig)); */ sig} match {
      case Pair(lhs, rhs)          =>
        recur(lhs) ~ recur(rhs)

      case Left(pair)             =>
        recur(pair) match {
          case PairV(lhs, rhs) => lhs
          case _ => ??? // imposiible
        }

      case Right(pair)            =>
        recur(pair) match {
          case PairV(lhs, rhs) => rhs
          case _ => ??? // imposiible
        }

      case At(vec, index)         =>
        recur(vec) match {
          case vec: VecV => Value(vec(index))
          case _ => ??? // imposiible
        }

      case Range(vec, to, from)   =>
        recur(vec) match {
          case vec: VecV =>  vec(to, from)
          case _ => ??? // imposiible
        }

      case VecLit(bits)           =>
        VecV(bits)

      case Var(sym, tpe)          =>
        env(sym)

      case Let(sym, sig, body)    =>
        val v = recur(sig)
        recur(body)(env.updated(sym, v))

      case Fsm(sym, init, body)   =>
        ??? // impossible after lifting

      case And(lhs, rhs)          =>
        and(recur(lhs), recur(rhs))

      case Or(lhs, rhs)           =>
        or(recur(lhs), recur(rhs))

      case Not(in)                =>
        not(recur(in))

      case Concat(lhs, rhs)     =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        VecV(lhsV.bits ++ rhsV.bits)

      case Equals(lhs, rhs)     =>
        equals(recur(lhs), recur(rhs))

      case Plus(lhs, rhs)       =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        plus(lhsV, rhsV)

      case Minus(lhs, rhs)      =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        minus(lhsV, rhsV)

      case Mux(cond, thenp, elsep)  =>
        val Value(bitV) = recur(cond)
        if (bitV == 1) recur(thenp)
        else recur(elsep)

      case Shift(lhs, rhs, isLeft)   =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        shift(lhsV, rhsV, isLeft)
    }


    import Phases._
    val normailized = inlining(anf(optsel(flatten(lift(body)))))
    // val normailized = inlining(anf(flatten(lift(body))))
    // println("after = " + normailized.show)

    normailized match {
      case fsm @ Fsm(sym, init, body) =>
        var lastState = init
        (vs: List[Value]) => {
          val env = input.map(_.sym).zip(vs).toMap + (sym -> lastState)
          // println(env)
          recur(body)(env) match {
            case PairV(lhs, rhs) =>
              lastState = lhs
              // println("out = " + rhs)
              rhs
            case vec: VecV =>  // after detupling
              val sepIndex = fsm.width
              lastState = vec(vec.width - 1, sepIndex)
              vec(sepIndex - 1, 0)
          }
        }

      case code => // combinational
        (vs: List[Value]) => recur(code)(input.map(_.sym).zip(vs).toMap)
    }

  }
}