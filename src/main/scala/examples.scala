package ysm

import lang._

import scala.language.implicitConversions

object examples {
  def halfAdder(a: Signal[Bit], b: Signal[Bit]): Signal[Vec[2]] = {
    val s = a ^ b
    val c = a & b
    Vec(c, s)
  }

  def fullAdder(a: Signal[Bit], b: Signal[Bit], cin: Signal[Bit]): Signal[Vec[2]] = {
    val ab   = halfAdder(a, b)
    val s    = halfAdder(ab(0), cin)
    val cout = ab(1) | s(1)
    Vec(cout, s(0))
  }

  def adder2(a: Signal[Vec[2]], b: Signal[Vec[2]]): Signal[Bit ~ Vec[2]] = {
    val cs0 = fullAdder(a(0), b(0), 0)
    val cs1 = fullAdder(a(1), b(1), cs0(1))
    cs1(1) ~ Vec(cs1(0), cs0(0))
  }
}