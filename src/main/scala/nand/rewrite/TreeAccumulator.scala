package nand
package rewrite

import core._
import Types._, Trees._

abstract class TreeAccumulator[X] {
  def apply[T <: Type](x: X, sig: Signal[T]): X

  def recur[T <: Type](x: X, tree: Signal[T]): X = tree match {
    case Par(lhs, rhs)          =>
      this(this(x, lhs), rhs)

    case Left(pair)             =>
      this(x, pair)

    case Right(pair)            =>
      this(x, pair)

    case At(vec, index)         =>
      this(x, vec)

    case Range(vec, to, from)   =>
      this(x, vec)

    case VecLit(bits)           =>
      x

    case Var(sym, tpe)          =>
      x

    case Let(sym, sig, body)    =>
      this(this(x, sig), body)

    case Fsm(sym, init, body)   =>
      this(x, body)

    case And(lhs, rhs)          =>
      this(this(x, lhs), rhs)

    case Or(lhs, rhs)           =>
      this(this(x, lhs), rhs)

    case Not(in)                =>
      this(x, in)

    case Concat(lhs, rhs)     =>
      this(this(x, lhs), rhs)

    case Equals(lhs, rhs)     =>
      this(this(x, lhs), rhs)

    case Plus(lhs, rhs)       =>
      this(this(x, lhs), rhs)

    case Minus(lhs, rhs)      =>
      this(this(x, lhs), rhs)

    case Mux(cond, thenp, elsep)  =>
      this(this(this(x, cond), thenp), elsep)

    case Shift(lhs, rhs, isLeft)   =>
      this(this(x, lhs), rhs)
  }
}
