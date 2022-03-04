package zeno

import scala.language.implicitConversions

import core._
import Types._, Trees._, Values._

import util._
import Printing._

import rewrite._

object lang {
  type Sig[T <: Type] = core.Sig[T]
  type Value             = core.Value

  type Type             =  Types.Type
  type Vec[T <: Num]    =  Types.VecT[T]
  type Num              =  Types.Num
  type Bit              =  Types.Bit

  type ~[S <: Type, T <: Type]    =  Types.PairT[S, T]

  def let[S <: Type, T <: Type](name: String, t: Sig[S])(fn: Sig[S] => Sig[T]): Sig[T] = {
    val sym = Symbol.fresh(name)
    Let(sym, t, fn(Var(sym, t.tpe)))
  }

  def let[S <: Type, T <: Type](t: Sig[S])(fn: Sig[S] => Sig[T]): Sig[T] =
    let("x", t)(fn)

  extension [S <: Type, T <: Type](t: Sig[S ~ T])
    def left: Sig[S] = Left(t)
    def right: Sig[T] = Right(t)

  extension [T <: Type](lhs: Sig[T])
    def ~ [U <: Type](rhs: Sig[U]): Sig[T ~ U] = Pair(lhs, rhs)

  extension (sig: Sig[_])
    def as[T <: Type]: Sig[T] = sig.as[T]

  extension [T <: Type](sig: Sig[T])
    def width: Int = sig.tpe match {
      case VecT(width) => width
      case _ => throw new Exception("access width on non-vector signal")
    }

  def fsm[S <: Type, T <: Type](name: String, init: Value)(next: Sig[S] => Sig[S ~ T]): Sig[T] = {
    val tpInit = Values.typeOf(init)
    val sym = Symbol.fresh(name)
    val body = next(Var(sym, tpInit))

    body.tpe match {
      case s ~ t =>
        if (s != tpInit) throw new Exception("incorrect type of FSM body. Expected = " + tpInit + ", found = " + s)

      case tp =>
        throw new Exception("unexpected type of FSM body. Pair type expected " + ", found = " + tp)
    }

    Fsm(sym, init, body)
  }

  def mux[T <: Type](cond: Sig[Bit], x: Sig[T], y: Sig[T]): Sig[T] = Mux(cond, x, y)

  extension [T <: Num](sig: Sig[Vec[T]])
    def unary_! : Sig[Vec[T]] = Not(sig)

  extension [T <: Num](lhs: Sig[Vec[T]])
    def & (rhs: Sig[Vec[T]]): Sig[Vec[T]] = And(lhs, rhs)
    def | (rhs: Sig[Vec[T]]): Sig[Vec[T]] = Or(lhs, rhs)
    def ^ (rhs: Sig[Vec[T]]): Sig[Vec[T]] = Or(And(lhs, !rhs), And(!lhs, rhs))

  extension (value: Value)
    def toSig[T <: Type]: Sig[T] = value match {
      case PairV(l, r) =>
        (l.toSig ~ r.toSig).asInstanceOf

      case VecV(bits)  =>
        VecLit(bits).asInstanceOf
    }

  inline def input[T <: Type](name: String): Var[T] =
    Var(Symbol(name), Types.typeOf[T])

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Sig[Bit]] = b => Vec(if b then 1 else 0)
  implicit val lit1: Conversion[1, Sig[Bit]] = one => Vec(1)
  implicit val lit0: Conversion[0, Sig[Bit]] = zero => Vec(0)

  /** Int -> Bits, take the least significant N bits */
  extension (n: Int)
    def W[N <: Num](using M: ValueOf[N]): Sig[Vec[N]] = {
      val N = M.value.asInstanceOf[Int]
      val bits = (0 until N).foldLeft(Nil: List[0|1]) { (acc, i) =>
        val bit: 0 | 1 = if (n & (1 << i)) == 0 then 0 else 1
        bit :: acc
      }
      VecLit(bits)
    }

  // ---------------- bit vector operations --------------------

  extension [M <: Num](vec: Sig[Vec[M]])
    def <<[N <: Num](amount: Sig[Vec[N]]): Sig[Vec[M]] =
      Shift(vec, amount, isLeft = true)

    def >>[N <: Num](amount: Sig[Vec[N]]): Sig[Vec[M]] =
      Shift(vec, amount, isLeft = false)

    def apply(index: Int): Sig[Bit] = At(vec, index)

  extension [N <: Num](lhs: Sig[Vec[N]])
    def + (rhs: Sig[Vec[N]]): Sig[Vec[N]] =
      Plus(lhs, rhs)

    def - (rhs: Sig[Vec[N]]): Sig[Vec[N]] =
      Minus(lhs, rhs)

  extension [M <: Num](lhs: Sig[Vec[M]])
    def ++ [N <: Num, U <: Num](rhs: Sig[Vec[N]]): Sig[Vec[U]] = Concat(lhs, rhs)

  extension [S <: Num](vec: Sig[Vec[S]])
    def apply[U <: Num](to: Int, from: Int): Sig[Vec[U]] = Range[S, U](vec, to, from)

  extension [T <: Num](x: Sig[Vec[T]])
    def === (y: Sig[Vec[T]]): Sig[Bit] = Equals(x, y)

  /** When syntax
   *
   *  when (a) {
   *
   *  } when (b) {
   *
   *  } otherwise {
   *
   *  }
   */
  def when[T <: Type](cond: Sig[Bit])(x: Sig[T]): WhenCont[T] =
    WhenCont { r => mux(cond, x, r) }
  class WhenCont[T <: Type](cont: Sig[T] => Sig[T]) {
    def otherwise(y: Sig[T]): Sig[T] = cont(y)

    def when (cond2: Sig[Bit])(y: Sig[T]): WhenCont[T] =
      WhenCont { r => cont(mux(cond2, y, r)) }
  }

  // ---------------- overloaded names --------------------

  object ~ {
    def unapply[S <: Type, T <: Type](sig: Sig[S ~ T]): (Sig[S], Sig[T]) =
      (sig.left, sig.right)

    def unapply(value: Value): Option[(Value, Value)] = value match {
      case PairV(lhs, rhs) => Some((lhs, rhs))
      case _ => None
    }

    def unapply(tp: Type): Option[(Type, Type)] = tp match {
      case p: PairT[_, _] => Some(p.lhs -> p.rhs)
      case _ => None
    }
  }

  object Vec {
    def apply[T <: Num](bit: 1 | 0, bits: (1 | 0)*): Sig[Vec[T]] =
      VecLit[T](bit :: bits.toList)

    def apply[T <: Num](bits: Sig[Bit]*): Sig[Vec[T]] =
      bits.foldRight(VecLit[T](Nil).as[Vec[T]]) { (bit, acc) =>
        bit ++ acc
      }

    def unapply(tp: Type): Option[Int] = tp match {
      case vec: Types.Vec[_] => Some(vec.width)
      case _ => None
    }
  }

  // ---------------- value operations --------------------

  object Value {
    def apply(bit: 0 | 1, bits: (0 | 1)*): Value =
      new VecV(bit :: bits.toList)

    def unapplySeq(value: Value): Option[List[0 | 1]] = value match {
      case VecV(bits) => Some(bits)
      case _ => None
    }
  }

  extension (lhs: Value)
    def ~ (rhs: Value): Value = new PairV(lhs, rhs)

  /** Int -> Bits */
  extension (n: Int)
    def toValue(N: Int): Value = {
      assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
      assert(n >= 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

      val bits = (0 until N).foldLeft(Nil: List[0|1]) { (acc, i) =>
        val bit: 0 | 1 = if (n & (1 << i)) == 0 then 0 else 1
        bit :: acc
      }

      VecV(bits)
    }

  extension (vec: Value)
    def toInt: Int = vec match {
      case vec: VecV =>
        (0 until vec.width).foldLeft(0) { (acc, i) => acc | ((vec(i) & 1) << i) }

      case _ =>
        throw new Exception("Cannot call .toInt on pairs")
    }

  extension (value: Value)
    def toShort: Short = value.toInt.toShort
    def toChar: Int = value.toInt.toChar

  // ---------------- transform operations --------------------

  extension [T <: Type](sig: Sig[T]) {
    def show: String = Printing.show(sig)

    def eval(inputs: Var[_]*): List[Value] => Value = Interpreter.eval(inputs.toList, sig)

    def toVerilog(moduleName: String,
                  inputs: Var[_]*): String = Verilog.emit(moduleName, inputs.toList, sig)
  }
}
