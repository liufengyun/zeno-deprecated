package nand
package core

import scala.compiletime._

object Types {
  sealed abstract class Type
  case class Pair[S <: Type, T <: Type](lhs: S, rhs: T) extends Type
  case class Vec[T <: Num](width: T) extends Type

  type ~[S <: Type, T <: Type] = Pair[S, T]
  type Bit = Vec[1]
  type Num = Int & Singleton

  inline def typeOf[T <: Type]: T = inline erasedValue[T] match {
    case _: ~[t1, t2]  =>
      (new Pair(typeOf[t1], typeOf[t2])).asInstanceOf

    case _: Vec[n]     =>
      val width = valueOf[n]
      Vec(width).asInstanceOf
  }
}