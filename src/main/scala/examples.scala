package ysm

import lang._

object examples {
  def halfAdder(a: Signal[Bit], b: Signal[Bit]): Signal[Vec[2]] = {
    val s = a ^ b
    val c = a & b
    Vec(c, s)
  }
}