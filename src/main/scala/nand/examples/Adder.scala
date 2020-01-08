package nand
package examples

import lang._

import scala.language.implicitConversions

object Adder {
  def halfAdder(a: Signal[Bit], b: Signal[Bit]): Signal[Vec[2]] = {
    val s = a ^ b
    val c = a & b
    c ++ s
  }

  def fullAdder(a: Signal[Bit], b: Signal[Bit], cin: Signal[Bit]): Signal[Vec[2]] = {
    val ab = halfAdder(a, b)
    val s = halfAdder(ab(0), cin)
    val cout = ab(1) | s(1)
    cout ++ s(0)

    // the version below generates smaller verilog code,
    // however, yosys can optimize the version above.

    // let( halfAdder(a, b) ) { ab =>
    //   let( halfAdder(ab(0), cin) ) { s =>
    //     val cout = ab(1) | s(1)
    //     cout ++ s(0)
    //   }
    // }

  }

  def adder2(a: Signal[Vec[2]], b: Signal[Vec[2]]): Signal[Vec[3]] = {
    val cs0 = fullAdder(a(0), b(0), 0)
    val cs1 = fullAdder(a(1), b(1), cs0(1))
    cs1(1) ++ cs1(0) ++ cs0(0)

    // let( fullAdder(a(0), b(0), 0) ) { cs0 =>
    //   let( fullAdder(a(1), b(1), cs0(1)) ) { cs1 =>
    //     cs1(1) ++ cs1(0) ++ cs0(0)
    //   }
    // }
  }

  def adderN[N <: Num](lhs: Signal[Vec[N]], rhs: Signal[Vec[N]]): Signal[Bit ~ Vec[N]] = {
    val n: Int = lhs.width

    def recur(index: Int, cin: Signal[Bit], acc: Signal[Vec[_]]): Signal[Bit ~ Vec[N]] =
      if (index >= n) cin ~ acc.as[Vec[N]]
      else {
        val cs: Signal[Vec[2]] = fullAdder(lhs(index), rhs(index), cin)
        recur(index + 1, cs(1), (cs(0) ++ acc.as[Vec[N]]).asInstanceOf)
      }

    recur(0, lit(false), Vec().as[Vec[_]])
  }
}