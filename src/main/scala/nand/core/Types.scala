package nand
package core

import scala.compiletime._

object Types {
  sealed abstract class Type
  case class PairT[S <: Type, T <: Type](lhs: S, rhs: T) extends Type
  case class VecT[T <: Num](width: T) extends Type

  type ~[S <: Type, T <: Type] = PairT[S, T]
  type Vec[T <: Num] = VecT[T]
  type Bit = VecT[1]
  type Num = Int & Singleton

  inline def typeOf[T <: Type]: T = inline erasedValue[T] match {
    case _: ~[t1, t2]  =>
      (new PairT(typeOf[t1], typeOf[t2])).asInstanceOf

    case _: VecT[n]     =>
      val width = valueOf[n]
      VecT(width).asInstanceOf
  }
}