package nand

import scala.language.implicitConversions

import core._
import Types._, Trees._, Values._

import util._
import Printing._

import rewrite._

object lang {
  type Signal = core.Signal
  type Value  = core.Value

  type Type   =  Types.Type
  type Vec    =  Types.Vec
  type ~      =  Types.~
  type Num    =  Types.Num
  type Bit    =  Types.Bit

  // TODO: dotty cannot resolve `Vec`
  import Types.Vec

  def let[S <: Type, T <: Type](name: String, t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] = {
    val sym = Symbol.fresh(name)
    Let(sym, t, fn(Var(sym, t.tpe)))
  }

  def let[S <: Type, T <: Type](t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] =
    let("x", t)(fn)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) left: Signal[S] = Left(t)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) right: Signal[T] = Right(t)

  def [T <: Type, U <: Type](lhs: Signal[T]) ~ (rhs: Signal[U]): Signal[T ~ U] = Par(lhs, rhs)

  object ~ {
    def unapply[S <: Type, T <: Type](sig: Signal[S ~ T]): (Signal[S], Signal[T]) =
      (sig.left, sig.right)

    def unapply(value: Value): Option[(Value, Value)] = value match {
      case PairV(lhs, rhs) => Some((lhs, rhs))
      case _ => None
    }
  }

  def [T <: Type](sig: Signal[_]) as: Signal[T] = sig.as[T]

  def [T <: Type](sig: Signal[T]) width: Int = sig.tpe match {
    case vec: Vec[_] => vec.width
    case _ => throw new Exception("access width on non-vector signal")
  }

  def fsm[S <: Type, T <: Type](name: String, init: Value)(next: Signal[S] => Signal[S ~ T]): Signal[T] = {
    val tpInit = Values.typeOf(init)
    val sym = Symbol.fresh(name)
    val body = next(Var(sym, tpInit))

    body.tpe match {
      case Pair(s, t) =>
        if (s != tpInit) throw new Exception("incorrect type of FSM body. Expected = " + tpInit + ", found = " + s)

      case tp =>
        throw new Exception("unexpected type of FSM body. Pair type expected " + ", found = " + tp)
    }

    Fsm(sym, init, body)
  }

  def mux[T <: Type](cond: Signal[Bit], x: Signal[T], y: Signal[T]): Signal[T] = Mux(cond, x, y)

  def [T <: Num](sig: Signal[Vec[T]]) unary_! : Signal[Vec[T]] = Not(sig)

  def [T <: Num](lhs: Signal[Vec[T]]) & (rhs: Signal[Vec[T]]): Signal[Vec[T]] = And(lhs, rhs)

  def [T <: Num](lhs: Signal[Vec[T]]) | (rhs: Signal[Vec[T]]): Signal[Vec[T]] = Or(lhs, rhs)

  def [T <: Num](lhs: Signal[Vec[T]]) ^ (rhs: Signal[Vec[T]]): Signal[Vec[T]] = Or(And(lhs, !rhs), And(!lhs, rhs))

  def [T <: Type](value: Value) toSignal: Signal[T] = value match {
    case PairV(l, r) =>
      (l.toSignal ~ r.toSignal).asInstanceOf

    case VecV(bits)  =>
      VecLit(bits).asInstanceOf
  }

  inline def input[T <: Type](name: String): Var[T] =
    Var(Symbol(name), Types.typeOf[T])

  def (lhs: Value) ~ (rhs: Value): Value =
    new PairV(lhs, rhs)

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Signal[Bit]] = b => Vec(if b then 1 else 0)
  implicit val lit1: Conversion[1, Signal[Bit]] = one => Vec(1)
  implicit val lit0: Conversion[0, Signal[Bit]] = zero => Vec(0)

  /** Int -> Bits */
  def (n: Int) toValue(N: Int): Value = {
    assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
    assert(n >= 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

    val bits = (0 until N).foldLeft(Nil: List[0|1]) { (acc, i) =>
      val bit: 0 | 1 = if (n & (1 << i)) == 0 then 0 else 1
      bit :: acc
    }

    VecV(bits)
  }

  /** Int -> Bits, take the least significant N bits */
  def [N <: Num](n: Int) W(implicit M: ValueOf[N]): Signal[Vec[N]] = {
    val N = M.value.asInstanceOf[Int]
    val bits = (0 until N).foldLeft(Nil: List[0|1]) { (acc, i) =>
      val bit: 0 | 1 = if (n & (1 << i)) == 0 then 0 else 1
      bit :: acc
    }
    VecLit(bits)
  }

  // ---------------- bit vector operations --------------------

  def [M <: Num, N <: Num](vec: Signal[Vec[M]]) << (amount: Signal[Vec[N]]): Signal[Vec[M]] =
    Shift(vec, amount, isLeft = true)

  def [M <: Num, N <: Num](vec: Signal[Vec[M]]) >> (amount: Signal[Vec[N]]): Signal[Vec[M]] =
    Shift(vec, amount, isLeft = false)

  def [N <: Num](lhs: Signal[Vec[N]]) + (rhs: Signal[Vec[N]]): Signal[Vec[N]] =
    Plus(lhs, rhs)

  def [N <: Num](lhs: Signal[Vec[N]]) - (rhs: Signal[Vec[N]]): Signal[Vec[N]] =
    Minus(lhs, rhs)

  def Vec[T <: Num](bit: 1 | 0, bits: (1 | 0)*): Signal[Vec[T]] =
    VecLit[T](bit :: bits.toList)

  def Vec[T <: Num](bits: Signal[Bit]*): Signal[Vec[T]] =
    bits.foldRight(VecLit[T](Nil).as[Vec[T]]) { (bit, acc) =>
      bit ++ acc
    }

  def [M <: Num, N <: Num, U <: Num](lhs: Signal[Vec[M]]) ++ (rhs: Signal[Vec[N]]): Signal[Vec[U]] = Concat(lhs, rhs)

  def [S <: Num](vec: Signal[Vec[S]]) apply(index: Int): Signal[Bit] = At(vec, index)

  def [S <: Num, U <: Num](vec: Signal[Vec[S]]) apply(to: Int, from: Int): Signal[Vec[U]] = Range[S, U](vec, to, from)

  def [T <: Num](x: Signal[Vec[T]]) === (y: Signal[Vec[T]]): Signal[Bit] = Equals(x, y)

  def [N <: Num](vec: Signal[Vec[N]]) width: Int = vec.tpe match {
    case _: Vec[_] => vec.width
    case _ => throw new Exception("Cannot call .width on a non-vector signal")
  }

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
  def when[T <: Type](cond: Signal[Bit])(x: Signal[T]): WhenCont[T] =
    WhenCont { r => mux(cond, x, r) }
  class WhenCont[T <: Type](cont: Signal[T] => Signal[T]) {
    def otherwise(y: Signal[T]): Signal[T] = cont(y)

    def when (cond2: Signal[Bit])(y: Signal[T]): WhenCont[T] =
      WhenCont { r => cont(mux(cond2, y, r)) }
  }

  // ---------------- value operations --------------------

  object Value {
    def apply(bit: 0 | 1, bits: (0 | 1)*): Value =
      new VecV(bit :: bits.toList)

    def unapplySeq[T <: Type](value: Value): Option[List[0 | 1]] = value match {
      case VecV(bits) => Some(bits)
      case _ => None
    }
  }

  def (vec: Value) toInt: Int = vec match {
    case vec: VecV =>
      (0 until vec.width).foldLeft(0) { (acc, i) => acc | ((vec(i) & 1) << i) }

    case _ =>
      throw new Exception("Cannot call .toInt on pairs")
  }

  def [T <: Num](value: Value) toShort: Short = value.toInt.toShort

  def [T <: Num](value: Value) toChar: Int = value.toInt.toChar

  // ---------------- transform operations --------------------

  def [T <: Type](sig: Signal[T]) show: String = Printing.show(sig)

  def [T <: Type](sig: Signal[T]) eval(inputs: Var[_]*): List[Value] => Value = Interpreter.eval(inputs.toList, sig)

  def [T <: Type](sig: Signal[T]) emitVerilog(moduleName: String, inputs: Var[_]*): String = Verilog.emit(moduleName, inputs.toList, sig)
}
