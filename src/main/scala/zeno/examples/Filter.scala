package zeno
package examples

import lang._

import scala.language.implicitConversions

object Filter {
  def delay[T <: Type](sig: Sig[T], init: Value): Sig[T] =
    fsm("s", init) { (last: Sig[T]) =>
      sig ~ last
    }

  def movingAverage(in: Sig[Vec[8]]): Sig[Vec[8]] = {
    let(delay(in, 0.toValue(8))) { z1 =>
      let(delay(z1, 0.toValue(8))) { z2 =>
        (z2 + (z1 << 1) + in) >> 2.toSig(2)
      }
    }
  }
}