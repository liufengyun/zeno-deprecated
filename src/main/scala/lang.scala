package ysm

import scala.language.implicitConversions

import scala.compiletime._

object lang {

  trait Circuit {
    type Exp[T]
    type Bit
    type ~[S, T]

    def let[S, T](name: String, t: Exp[S])(fn: Exp[S] => Exp[T]): Exp[T]
    def pair[S, T](t1: Exp[S], t2: Exp[T]): Exp[S ~ T]
    def left[S, T](t: Exp[(S, T)]): Exp[S]
    def right[S, T](t: Exp[(S, T)]): Exp[T]
    def fsm[S, T](name: String, v: Exp[S])(fn: Exp[S] => Exp[S ~ T]): Exp[T]

    def lit(v: Boolean): Exp[Bit]
    def and(a: Exp[Bit], b: Exp[Bit]): Exp[Bit]
    def or(a: Exp[Bit], b: Exp[Bit]): Exp[Bit]
    def not(t: Exp[Bit]): Exp[Bit]
  }

  given stdlib: (c: Circuit) => StdLib[c.type] = new StdLib(c)

  class StdLib[T <: Circuit](val c: T) {
    import c._

    type Bit8 = Exp[Bit ~ Bit ~ Bit ~ Bit ~ Bit ~ Bit ~ Bit ~ Bit]

    // Boolean -> Bit
    implicit val lit2Exp: Conversion[Boolean, Exp[Bit]] = lit(_)

    def [S, T] (t1: Exp[S]) ~(t2: Exp[T]): Exp[S ~ T] = pair(t1, t2)

    def (t1: Exp[Bit]) && (t2: Exp[Bit]): Exp[Bit] = and(t1, t2)
    def (t1: Exp[Bit]) || (t2: Exp[Bit]): Exp[Bit] = or(t1, t2)
    def (t: Exp[Bit]) not : Exp[Bit] = not(t)

    def [S, T] (t: Exp[S ~ T]) left: Exp[S] = left(t)
    def [S, T] (t: Exp[S ~ T]) right : Exp[T] = right(t)

    // Tuple -> Pair
    implicit def tuple2toPair[S, T]: Conversion[(Exp[S], Exp[T]), Exp[S ~ T]] =
      t2 => t2._1 ~ t2._2

    implicit def tuple3toPair[T1, T2, T3]: Conversion[(Exp[T1], Exp[T2], Exp[T3]), Exp[T1 ~ T2 ~ T3]] =
      t3 => t3._1 ~ t3._2 ~ t3._3

    def mux1(cond: Exp[Bit], x: Exp[Bit], y: Exp[Bit]): Exp[Bit] = (cond.not || x) && (cond || y)
    inline def mux[T](cond: Exp[Bit], x: Exp[T], y: Exp[T]): Exp[T] = inline erasedValue[T] match {
      case _: ~[t1, t2] =>
        val x1 = x.asInstanceOf[Exp[t1 ~ t2]]
        val y1 = y.asInstanceOf[Exp[t1 ~ t2]]
        (mux(cond, x1.left, y1.left) ~ mux(cond, x1.right, y1.right)).asInstanceOf[Exp[T]]

      case _: Bit       =>
        mux1(cond, x.asInstanceOf[Exp[Bit]], y.asInstanceOf[Exp[Bit]]).asInstanceOf[Exp[T]]
    }

    def equalBit(x: Exp[Bit], y: Exp[Bit]): Exp[Bit] = (x && y) || (x.not && y.not)
    inline def [T](x: Exp[T]) === (y: Exp[T]): Exp[Bit] = inline erasedValue[T] match {
      case _: ~[t1, t2] =>
        val x1 = x.asInstanceOf[Exp[t1 ~ t2]]
        val y1 = y.asInstanceOf[Exp[t1 ~ t2]]
        x1.left === y1.left && x1.right === y1.right

      case _: Bit       =>
        equalBit(x.asInstanceOf[Exp[Bit]], y.asInstanceOf[Exp[Bit]])
    }
  }
}