package nand
package rewrite

import lang._

import core._
import Trees._, Types._, Values._

// TODO: dotty cannot resolve `Vec`
import Types.Vec

object Phases {

  def fix[T <: AnyRef](v: T)(fn: T => T): T = {
    val current = fn(v)
    if (v `ne` current) fix(current)(fn)
    else current
  }

  def lift[T <: Type](sig: Signal[T]): Signal[T] = {
    val liftMap = new TreeMap {
      def apply[T <: Type](tree: Signal[T]): Signal[T] = tree match {
        case And(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs & x.right) } )

        case And(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right & rhs) } )

        case Or(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs | x.right) } )

        case Or(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right | rhs) } )

        case Par(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs ~ x.right) } )

        case Par(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right ~ rhs) } )

        case Minus(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs - x.right) } )

        case Minus(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right - rhs) } )

        case Plus(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs + x.right) } )

        case Plus(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right + rhs) } )

        case Not(Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (!x.right) } )

        case Left(Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right.left) } )

        case Right(Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right.right) } )

        case At(Fsm(sym, init, body), index) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right(index)) } )

        case Range(Fsm(sym, init, body), to, from) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right(to, from)).as[T] } )

        case Equals(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs.as[Vec[0]] === x.right.as[Vec[0]]).as[T] } )

        case Equals(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right.as[Vec[0]] === rhs.as[Vec[0]]).as[T] } )

        case Concat(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs ++ x.right).as[T] } )

        case Concat(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right ++ rhs).as[T] } )

        case Shift(lhs, Fsm(sym, init, body), isLeft) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ Shift(lhs, x.right, isLeft) } )

        case Shift(Fsm(sym, init, body), rhs, isLeft) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ Shift(x.right, rhs, isLeft) } )

        case Mux(Fsm(sym, init, body), thenp, elsep) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ Mux(x.right, thenp, elsep) } )

        case Mux(lhs, Fsm(sym, init, body), elsep) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ Mux(lhs, x.right, elsep) } )

        case Mux(lhs, thenp, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ Mux(lhs, thenp, x.right) } )

        case Let(sym, Fsm(sym1, init, body1), body) =>
          Fsm(sym1, init, let("x", body1) { x =>
            Let(sym, x.right, x.left ~ body)
          })

        case Let(sym, sig, Fsm(sym1, init, body)) =>
          Fsm(sym1, init, Let(sym, sig, body))

        case _ =>
          recur(tree)
      }
    }

    fix(sig)(liftMap.apply[T])
  }


  /** Flatten a lifted tree
   *
   *  It must happen before detupling.
   */
  def flatten[T <: Type](tree: Signal[T]): Signal[T] = tree match {
    case Fsm(sym1, init1, fsm2 @ Fsm(_, _, _)) =>
      val fsm2a @ Fsm(sym2, init2, body2) = flatten(fsm2)

      fsm(sym1.name + "_" + sym2.name, init1 ~ init2) { (state: Signal[T]) =>
        Let(sym1, state.as[T ~ T].left,
          Let(sym2, state.as[T ~ T].right,
            let("x", body2.as[T ~ (T ~ T)]) { x =>
              ((x.right.left ~ x.left) ~ x.right.right).as[T ~ T]
            }
          )
        )

      }

    case _ => tree
  }

  def detuple[T <: Type, U <: Num](sig: Signal[T]): Signal[Vec[U]] = {
    def toVecType(tp: Type): Vec[_] = tp match {
      case Pair(lhs, rhs) =>
        (toVecType(lhs), toVecType(rhs)) match {
          case (Vec(m), Vec(n)) =>
            val width = m + n
            Vec(width)
        }

      case tp: Vec[_] =>
        tp
    }

    def toVecValue(v: Value): VecV = v match {
      case PairV(lhs, rhs) =>
        (toVecValue(lhs), toVecValue(rhs)) match {
          case (VecV(bits1), VecV(bits2)) => VecV(bits1 ++ bits2)
        }

      case v: VecV =>
        v
    }


    def recur[T <: Type, U <: Num](sig: Signal[T]): Signal[Vec[U]] = sig match {
      case Par(lhs, rhs)          =>
        (recur(lhs) ++ recur(rhs)).as[Vec[U]]

      case Left(pair)             =>
        val vec = recur(pair)
        val tp = toVecType(sig.tpe)
        vec(vec.width - 1, vec.width - tp.width)

      case Right(pair)            =>
        val vec = recur(pair)
        val tp = toVecType(sig.tpe)
        vec(tp.width - 1, 0)

      case At(vec, index)         =>
        // vec may contain tuples
        val vec1 = recur(vec)
        vec1(index).as[Vec[U]]

      case Range(vec, to, from)   =>
        // vec may contain tuples
        val vec1 = recur(vec)
        vec1(to, from).as[Vec[U]]

      case VecLit(_)              =>
        sig.as[Vec[U]]

      case Var(sym, tpe)          =>
        Var(sym, toVecType(tpe))

      case Let(sym, sig, body)    =>
        val sig2 = recur(sig)
        val body2 = recur(body)
        Let(sym, sig2, body2.as[Vec[U]])

      case Fsm(sym, init, body)   =>
        val init2 = toVecValue(init)
        val body2 = recur(body)
        Fsm(sym, init2, body2.asInstanceOf)

      case And(lhs, rhs)          =>
        And(recur(lhs), recur(rhs))

      case Or(lhs, rhs)           =>
        Or(recur(lhs), recur(rhs))

      case Not(in)                =>
        Not(recur(in))

      case Concat(lhs, rhs)     =>
        recur(lhs) ++ recur(rhs)

      case Equals(lhs, rhs)     =>
        Equals(recur(lhs), recur(rhs)).as[Vec[U]]

      case Plus(lhs, rhs)       =>
        // x.1 possible in `lhs`
        Plus(recur(lhs), recur(rhs))

      case Minus(lhs, rhs)      =>
        // x.1 possible in `lhs`
        Minus(recur(lhs), recur(rhs))

      case Mux(cond, thenp, elsep)  =>
        // x.1 possible in `cond`
        Mux(recur(cond), recur(thenp), recur(elsep))

      case Shift(lhs, rhs, isLeft)   =>
        // x.1 possible in `lhs`
        Shift(recur(lhs), recur(rhs), isLeft)
    }

    optsel(recur(sig).as[Vec[U]])
  }

  /** Optimize range and index operation that follows concatenation
   *
   *  (vec10 ++ vec5)[3]     ~~>     vec10[3]
   *  (vec5 ++ vec4)[6..3]   ~~>     vec5[2:0] ++ vec4[3]
   *  vec[6..6]              ~~>     vec[6]
   *  vec[6..3][3..2]        ~~>     vec[6..5]
   *  vec[6..3][2]           ~~>     vec[5]
   *  vec ++ []              ~~>     vec
   *  [] ++ vec              ~~>     vec
   *  (vec1 ~ vec2).left     ~~>     vec1
   *  (vec1 ~ vec2).right    ~~>     vec2
   */
  def optsel[T <: Type](sig: Signal[T]): Signal[T] = {
    val rangeOptMap = new TreeMap {
      def apply[T <: Type](tree: Signal[T]): Signal[T] = tree match {
        case At(Concat(lhs, rhs), index) =>
          if (index < rhs.width) At(rhs, index)
          else At(rhs, index - rhs.width)

        case At(vec, 0) if vec.width == 1 =>
          vec.as[T]

        case Range(Concat(lhs, rhs), hi, lo) =>
          val rhsWdith = rhs.width
          if (hi < rhsWdith && lo < rhsWdith) Range(rhs, hi, lo).as[T]
          else if (hi >= rhsWdith && lo >= rhsWdith) Range(lhs, hi - rhsWdith, lo - rhsWdith).as[T]
          else if (hi >= rhsWdith && lo < rhsWdith) {
            Range(lhs, hi - rhsWdith, 0) ++ Range(rhs, rhsWdith - 1, lo)
          }.as[T]
          else ??? // impossible

        case Range(Range(vec, hi1, lo1), hi2, lo2) =>
          val hi = hi2 + lo1
          val lo = lo2 + lo1
          Range(vec, hi, lo).as[T]

        case Range(vec, hi, lo) =>
          if (hi == lo) At(vec, hi).as[T]
          else if (lo == 0 && hi == vec.width - 1) vec.as[T]
          else tree

        case At(Range(vec, hi, lo), index) =>
          val index2 = index + lo
          At(vec, index2)

        case Concat(lhs, rhs) if lhs.width == 0 => rhs.as[T]

        case Concat(lhs, rhs) if rhs.width == 0 => lhs.as[T]

        case Left(Par(lhs, rhs)) => lhs

        case Right(Par(lhs, rhs)) => rhs

        case _ =>
          recur(tree)
      }
    }

    fix(sig)(rangeOptMap.apply[T])
  }

  object ANF {
    def unapply[T <: Type](sig: Signal[T]): Boolean = sig match {
      case Var(_, _)        => true
      case At(vec, _)       => unapply(vec)
      case Range(vec, _, _) => unapply(vec)
      case Concat(lhs, rhs) => unapply(lhs) && unapply(rhs)
      case Par(lhs, rhs)    => unapply(lhs) && unapply(rhs)
      case Left(pair)       => unapply(pair)
      case Right(pair)      => unapply(pair)
      case VecLit(_)        => true
      case _                => false
    }
  }

  /** A Normal Form
   *
   *  Precondition: all FSMs must be lifted
   */
  def anf[T <: Type](sig: Signal[T]): Signal[T] = {
    def anfize[S <: Type, T <: Type](sig: Signal[S])(cont: Signal[S] => Signal[T]): Signal[T] =
      sig match {
        case ANF() =>
          cont(sig)

        case Let(sym, sig2, body) =>
          Let(sym, sig2, recur(body)(cont))

        case _ =>
          recur(sig) { sig2 => let(sig2)(cont) }
      }

    def recur[S <: Type, T <: Type](tree: Signal[S])(cont: Signal[S] => Signal[T]): Signal[T] = tree match {
        case ANF() =>
          cont(tree)

        case Par(lhs, rhs)          =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Par(lhs2, rhs2))
            }
          }

        case Left(pair)             =>
          anfize(pair) { pair2 =>
            if (pair.eq(pair2)) cont(tree)
            else cont(Left(pair2))
          }

        case Right(pair)            =>
          anfize(pair) { pair2 =>
            if (pair.eq(pair2)) cont(tree)
            else cont(Right(pair2))
          }

        case At(vec, index)         =>
          anfize(vec) { vec2 =>
            if (vec.eq(vec2)) cont(tree)
            else cont(At(vec2, index))
          }

        case Range(vec, to, from)   =>
          anfize(vec) { vec2 =>
            if (vec.eq(vec2)) cont(tree)
            else cont(Range(vec2, to, from).as[S])
          }

        case Let(sym, sig, body)    =>
          anfize(sig) { sig2 =>
            val body2 = anfize(body)(identity)
            if (sig.eq(sig2) && body.eq(body2)) cont(tree)
            else cont(Let(sym, sig2, body2))
          }

        case Fsm(sym, init, body)   =>
          anfize(body) { body2 =>
            if (body.eq(body2)) cont(tree)
            else Fsm(sym, init, body2.as)
          }

        case And(lhs, rhs)          =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(And(lhs2, rhs2))
            }
          }

        case Or(lhs, rhs)           =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Or(lhs2, rhs2))
            }
          }

        case Not(in)                =>
          anfize(in) { in2 =>
            if (in.eq(in2)) cont(tree)
            else cont(Not(in2))
          }

        case Concat(lhs, rhs)     =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Concat(lhs2, rhs2).as[S])
            }
          }

        case Equals(lhs, rhs)     =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Equals(lhs2, rhs2))
            }
          }

        case Plus(lhs, rhs)       =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Plus(lhs2, rhs2))
            }
          }

        case Minus(lhs, rhs)      =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Minus(lhs2, rhs2))
            }
          }

        case Mux(cond, thenp, elsep)  =>
          anfize(cond) { cond2 =>
            anfize(thenp) { thenp2 =>
              anfize(elsep) { elsep2 =>
                if (cond.eq(cond2) && thenp.eq(thenp2) && elsep.eq(elsep2)) cont(tree)
                else cont(Mux(cond2, thenp2, elsep2))
              }
            }
          }

        case Shift(lhs, rhs, isLeft)   =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Shift(lhs2, rhs2, isLeft))
            }
          }

        case _ =>
          ??? // impossible
      }

    // fix(sig)(anfMap.apply[T])
    recur(sig)(identity)
  }

  /** Inlining
   *
   *  Precondition: tree must be ANF
   */
  def inlining[T <: Type](sig: Signal[T]): Signal[T] = {
    def usageCount[T <: Type](sym: Symbol, tree: Signal[T]): Int = {
      val counter = new TreeAccumulator[Int] {
        def apply[T  <: Type](x: Int, tree: Signal[T]): Int = tree match {
          case Var(sym1, _) =>
            if (sym.eq(sym1)) x + 1
            else x
          case _ => recur(x, tree)
        }
      }
      counter(0, tree)
    }

    val inliningMap = new TreeMap {
      import java.util.IdentityHashMap
      val map: IdentityHashMap[Symbol, Signal[_]] = new IdentityHashMap()

      def apply[T <: Type](tree: Signal[T]): Signal[T] = tree match {
        case Let(sym, rhs @ ANF(), body) =>
          map.put(sym, rhs)
          recur(body)

        case Let(sym, rhs, body) =>
          val count = usageCount(sym, body)
          if (count == 0) recur(body) // dead code elimination
          else if (count == 1) {
            map.put(sym, rhs)
            recur(body)
          }
          else recur(tree)

        case Var(sym, tpe) =>
          if (map.containsKey(sym)) map.get(sym).as[T]
          else tree

        case _ =>
          recur(tree)
      }
    }

    fix(sig)(inliningMap.apply[T])
  }
}
