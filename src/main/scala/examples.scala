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

  def adder2(a: Signal[Vec[2]], b: Signal[Vec[2]]): Signal[Vec[3]] = {
    val cs0 = fullAdder(a(0), b(0), 0)
    val cs1 = fullAdder(a(1), b(1), cs0(1))
    Vec(cs1(1), cs1(0), cs0(0))
  }

  def adderN[N <: Num](vec1: Signal[Vec[N]], vec2: Signal[Vec[N]]): Signal[Bit ~ Vec[N]] = {
    val n: Int = vec1.size

    // index starts from least significant bit
    def recur(index: Int, cin: Signal[Bit], acc: Signal[Vec[_]]): (Signal[Bit], Signal[Vec[N]]) =
      if (index >= n) (cin, acc.as[Vec[N]])
      else {
        val a: Signal[Bit] = vec1(index).as[Bit]
        val b: Signal[Bit] = vec2(index).as[Bit]
        val s: Signal[Bit] = a ^ b ^ cin
        val cout: Signal[Bit] = (a & b ) | (cin & (a ^ b))
        recur(index + 1, cout, (s :: acc.as[Vec[N]]).asInstanceOf)
      }

    recur(0, lit(false), Vec().as[Vec[_]])
  }
}