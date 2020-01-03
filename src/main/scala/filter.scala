package ysm

import lang._

import scala.language.implicitConversions

object Filter {
  def delay[T <: Type](sig: Signal[T], init: Value): Signal[T] =
    fsm("delay", init) { (last: Signal[T]) =>
      sig ~ last
    }

  def movingAverage(in: Signal[Vec[8]]): Signal[Vec[8]] = {
    let(in) { z0 =>
      let(delay(z0, 0.toValue(8))) { z1 =>
        let(delay(z1, 0.toValue(8))) { z2 =>
          (z2 + (z1 << 1) + z0) >> 2.W[2]
        }
      }
    }
  }
}