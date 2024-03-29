package zeno
package rewrite

import lang._

import core._
import Trees._, Types._, Values._

import util._

import scala.annotation.tailrec

object Phases {

  @tailrec
  def fix[T <: AnyRef](v: T)(fn: T => T): T = {
    val current = fn(v)
    if (v `ne` current) fix(current)(fn)
    else current
  }

  def lift[T <: Type](sig: Sig[T]): Sig[T] = {
    val liftMap = new TreeMap {
      def apply[T <: Type](tree: Sig[T]): Sig[T] = tree match {
        case And(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs & x.right) } )

        case And(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right & rhs) } )

        case Or(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs | x.right) } )

        case Or(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right | rhs) } )

        case Pair(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs ~ x.right) } )

        case Pair(Fsm(sym, init, body), rhs) =>
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
  def flatten[T <: Type](tree: Sig[T]): Sig[T] = tree match {
    case Fsm(sym1, init1, fsm2 @ Fsm(_, _, _)) =>
      val fsm2a @ Fsm(sym2, init2, body2) = flatten(fsm2)

      fsm(sym1.name + "_" + sym2.name, init1 ~ init2) { (state: Sig[T]) =>
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

  def detuple[T <: Type, U <: Num](sig: Sig[T]): Sig[Vec[U]] = {
    def toVecType(tp: Type): Vec[_] = tp match {
      case PairT(lhs, rhs) =>
        (toVecType(lhs), toVecType(rhs)) match {
          case (VecT(m), VecT(n)) =>
            val width = m + n
            VecT(width)
        }

      case tp: VecT[_] =>
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


    def recur[T <: Type, U <: Num](sig: Sig[T]): Sig[Vec[U]] = sig match {
      case Pair(lhs, rhs)          =>
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
  def optsel[T <: Type](sig: Sig[T]): Sig[T] = {
    val rangeOptMap = new TreeMap {
      def apply[T <: Type](tree: Sig[T]): Sig[T] = tree match {
        case At(Concat(lhs, rhs), index) =>
          if (index < rhs.width) At(recur(rhs), index)
          else At(recur(lhs), index - rhs.width)

        case At(vec, 0) if vec.width == 1 =>
          recur(vec).as[T]

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
          Range(recur(vec), hi, lo).as[T]

        case Range(vec, hi, lo) =>
          if (hi == lo) At(recur(vec), hi).as[T]
          else if (lo == 0 && hi == vec.width - 1) recur(vec).as[T]
          else recur(tree)

        case At(Range(vec, hi, lo), index) =>
          val index2 = index + lo
          At(recur(vec), index2)

        case Concat(lhs, rhs) if lhs.width == 0 => recur(rhs).as[T]

        case Concat(lhs, rhs) if rhs.width == 0 => recur(lhs).as[T]

        case Left(Pair(lhs, rhs)) => recur(lhs)

        case Right(Pair(lhs, rhs)) => recur(rhs)

        case _ =>
          recur(tree)
      }
    }

    fix(sig)(rangeOptMap.apply[T])
  }

  object ANFAtom {
    def unapply[T <: Type](sig: Sig[T]): Boolean = sig match {
      case Var(_, _)        => true
      case At(vec, _)       => unapply(vec)
      case Range(vec, _, _) => unapply(vec)
      case Concat(lhs, rhs) => unapply(lhs) && unapply(rhs)
      case Pair(lhs, rhs)   => unapply(lhs) && unapply(rhs)
      case Left(pair)       => unapply(pair)
      case Right(pair)      => unapply(pair)
      case VecLit(_)        => true
      case _                => false
    }
  }

  /** A Normal Form
   *
   *  Precondition: all FSMs must be flattened
   *
   *  A ::= x | A[i] | A[j..i] | A ~ A | A ++ A | A.1 | A.2 | 010
   *  M ::= A | A + A | A - A | A << A | A >> A | A & A\/A | A | !A | A == A | if (A) A else A
   *  E ::= M | let x = M in E
   *  N ::= E | fsm { v | s => N }
   */
  def anf[T <: Type](sig: Sig[T]): Sig[T] = {
    // the argument to cont should be an ANF atom, it returns an ANF expression
    def atomize[S <: Type, T <: Type](tree: Sig[S])(cont: Sig[S] => Sig[T]): Sig[T] =
      moleculize(tree) {
        case ANFAtom() =>
          cont(tree)

        case sig =>
          let(sig)(cont)
      }


    // the argument to cont should be an ANF molecule, it returns ANF expression
    def moleculize[S <: Type, T <: Type](tree: Sig[S])(cont: Sig[S] => Sig[T]): Sig[T] = Tracing.trace("ANF " + tree.show) {
      tree match {
        case ANFAtom() =>
          cont(tree)

        case Pair(lhs, rhs)          =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Pair(lhs2, rhs2))
            }
          }

        case Left(pair)             =>
          atomize(pair) { pair2 =>
            if (pair.eq(pair2)) cont(tree)
            else cont(Left(pair2))
          }

        case Right(pair)            =>
          atomize(pair) { pair2 =>
            if (pair.eq(pair2)) cont(tree)
            else cont(Right(pair2))
          }

        case At(vec, index)         =>
          atomize(vec) { vec2 =>
            if (vec.eq(vec2)) cont(tree)
            else cont(At(vec2, index))
          }

        case Range(vec, to, from)   =>
          atomize(vec) { vec2 =>
            if (vec.eq(vec2)) cont(tree)
            else cont(Range(vec2, to, from).as[S])
          }

        case Let(sym, sig, body)    =>
          moleculize(sig) { sig2 =>
            val body2 = moleculize(body)(cont)
            if (sig.eq(sig2) && body.eq(body2)) tree.as[T]
            else Let(sym, sig2, body2)
          }

        case Fsm(sym, init, body)   =>
          val body2 = moleculize(body)(identity) // assumption: FSM are lifted
          if (body.eq(body2)) tree.as[T]
          else Fsm(sym, init, body2.as)

        case And(lhs, rhs)          =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(And(lhs2, rhs2))
            }
          }

        case Or(lhs, rhs)           =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Or(lhs2, rhs2))
            }
          }

        case Not(in)                =>
          atomize(in) { in2 =>
            if (in.eq(in2)) cont(tree)
            else cont(Not(in2))
          }

        case Concat(lhs, rhs)     =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Concat(lhs2, rhs2).as[S])
            }
          }

        case Equals(lhs, rhs)     =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Equals(lhs2, rhs2))
            }
          }

        case Plus(lhs, rhs)       =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Plus(lhs2, rhs2))
            }
          }

        case Minus(lhs, rhs)      =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Minus(lhs2, rhs2))
            }
          }

        case Mux(cond, thenp, elsep)  =>
          atomize(cond) { cond2 =>
            atomize(thenp) { thenp2 =>
              atomize(elsep) { elsep2 =>
                if (cond.eq(cond2) && thenp.eq(thenp2) && elsep.eq(elsep2)) cont(tree)
                else cont(Mux(cond2, thenp2, elsep2))
              }
            }
          }

        case Shift(lhs, rhs, isLeft)   =>
          atomize(lhs) { lhs2 =>
            atomize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) cont(tree)
              else cont(Shift(lhs2, rhs2, isLeft))
            }
          }

        case _ =>
          ??? // impossible
      }
    }

    // fix(sig)(sig => moleculize(sig)(identity))
    moleculize(sig)(identity)
  }

  /** Inlining
   *
   *  Precondition: tree must be ANF
   */
  def inlining[T <: Type](sig: Sig[T]): Sig[T] = {
    def usageCount[T <: Type](sym: Symbol, tree: Sig[T]): Int = {
      val counter = new TreeAccumulator[Int] {
        def apply[T  <: Type](x: Int, tree: Sig[T]): Int = tree match {
          case Var(sym1, _) =>
            if (sym.eq(sym1)) x + 1
            else x
          case _ => recur(x, tree)
        }
      }
      counter(0, tree)
    }

    // Why ANF before inlining? And why two phase inlining?
    //
    // let x = (a + b) ~ (c + d)
    // in x.1 + x.2

    val inliningMapAtom = new TreeMap {
      import java.util.IdentityHashMap
      val map: IdentityHashMap[Symbol, Sig[_]] = new IdentityHashMap()

      def apply[T <: Type](tree: Sig[T]): Sig[T] = tree match {
        case Let(sym, rhs @ ANFAtom(), body) =>
          map.put(sym, this(rhs))
          this(body)

        case Var(sym, tpe) =>
          if (map.containsKey(sym)) map.get(sym).as[T]
          else tree

        case _ =>
          recur(tree)
      }
    }

    val inliningMapMolecule = new TreeMap {
      import java.util.IdentityHashMap
      val map: IdentityHashMap[Symbol, Sig[_]] = new IdentityHashMap()

      def apply[T <: Type](tree: Sig[T]): Sig[T] = tree match {
        case Let(sym, rhs, body) =>
          val count = usageCount(sym, body)
          if (count == 0) this(body) // dead code elimination
          else if (count == 1) {
            map.put(sym, this(rhs))
            this(body)
          }
          else recur(tree)

        case Var(sym, tpe) =>
          if (map.containsKey(sym)) map.get(sym).as[T]
          else tree

        case _ =>
          recur(tree)
      }
    }


    val sig2 = fix(sig) { sig =>
      optsel(inliningMapAtom(sig))
    }

    fix(sig2) { sig =>
      inliningMapMolecule(sig)
    }
  }

  def size[T <: Type](sig: Sig[T]): Int = {
    val counter = new TreeAccumulator[Int] {
      def apply[T <: Type](x: Int, sig: Sig[T]): Int =
        recur(x + 1, sig)
    }
    counter(0, sig)
  }
}
