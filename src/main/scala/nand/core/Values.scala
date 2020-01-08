package nand
package core

import Types._

sealed abstract class Value

private[nand] object Values {
  case class PairV(lhs: Value, rhs: Value) extends Value

  case class VecV(bits: List[0 | 1]) extends Value {
    // bits are stored in reverse order
    def apply(i: Int): 0 | 1 = bits(width - i - 1)
    def width: Int = bits.size
    def apply(to: Int, from: Int): VecV =
      VecV(bits.dropRight(from).drop(bits.size - to - 1))
  }

  def typeOf(value: Value): Type = value match {
    case PairV(l, r)  =>
      new PairT(typeOf(l), typeOf(r))

    case VecV(bits)   =>
      val width = bits.size
      VecT(width)
  }
}