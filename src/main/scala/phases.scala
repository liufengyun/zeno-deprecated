package ysm

import lang._

object phases {
  abstract class TreeMap {
    def apply[T <: Type](sig: Signal[T]): Signal[T]

    def recur[T <: Type](tree: Signal[T]): Signal[T] = tree match {
      case Par(lhs, rhs)          =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Par(lhs2, rhs2)

      case Left(pair)             =>
        val pair2 = this(pair)
        if (pair2.eq(pair)) tree
        else Left(pair2)

      case Right(pair)            =>
        val pair2 = this(pair)
        if (pair2.eq(pair)) tree
        else Right(pair2)

      case At(vec, index)         =>
        val vec2 = this(vec)
        if (vec2.eq(vec)) tree
        else At(vec2, index)

      case Range(vec, to, from)   =>
        val vec2 = this(vec)
        if (vec2.eq(vec)) tree
        else Range(vec2, to, from).as[T]

      case VecLit(bits)           =>
        tree

      case Var(sym, tpe)          =>
        tree

      case Let(sym, sig, body)    =>
        val sig2 = this(sig)
        val body2 = this(body)
        if (sig2.eq(sig) && body2.eq(body)) tree
        else Let(sym, sig2, body2)

      case Fsm(sym, init, body)   =>
        val body2 = this(body)
        if (body2.eq(body)) tree
        else Fsm(sym, init, body2)

      case And(lhs, rhs)          =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else And(lhs2, rhs2)

      case Or(lhs, rhs)           =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Or(lhs2, rhs2)

      case Not(in)                =>
        val in2 = this(in)
        if (in2.eq(in)) tree
        else Not(in2)

      case Concat(lhs, rhs)     =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Concat(lhs2, rhs2).as[T]

      case Equals(lhs, rhs)     =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Equals(lhs2, rhs2)

      case Plus(lhs, rhs)       =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Plus(lhs2, rhs2)

      case Minus(lhs, rhs)      =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Minus(lhs2, rhs2)

      case Mux(cond, thenp, elsep)  =>
        val cond2   = this(cond)
        val thenp2  = this(thenp)
        val elsep2  = this(elsep)
        if (cond2.eq(cond) && thenp2.eq(thenp) && elsep2.eq(elsep)) tree
        else Mux(cond2, thenp2, elsep2)

      case Shift(lhs, rhs, isLeft)   =>
        val lhs2 = this(lhs)
        val rhs2 = this(rhs)
        if (lhs2.eq(lhs) && rhs2.eq(rhs)) tree
        else Shift(lhs2, rhs2, isLeft)

    }
  }

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
        Let(sym1, state.asPair.left,
          Let(sym2, state.asPair.right,
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
            val size = m + n
            Vec(size)
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
        vec(vec.size - 1, vec.size - tp.size)

      case Right(pair)            =>
        val vec = recur(pair)
        val tp = toVecType(sig.tpe)
        vec(tp.size - 1, 0)

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

    recur(sig).as[Vec[U]]
  }

  /** Optimize range and index operation that follows concatenation
   *
   *  (vec10 ++ vec5)[3]     ~~>     vec10[3]
   *  (vec5 ++ vec4)[6..3]   ~~>     vec5[2:0] ++ vec4[3]
   *  vec[6..6]              ~~>     vec[6]
   *  vec[6..3][3..2]        ~~>     vec[6..5]
   *  vec[6..3][2]           ~~>     vec[5]
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

        case _ =>
          recur(tree)
      }
    }

    fix(sig)(rangeOptMap.apply[T])
  }

  /** A Normal Form
   *
   *  Precondition: all FSMs must be lifted
   */
  def anf[T <: Type](sig: Signal[T]): Signal[T] = {
    def anfize[S <: Type, T <: Type](sig: Signal[S])(cont: Signal[S] => Signal[T]): Signal[T] =
      sig match {
        case x: Var[_] => cont(x)
        case Let(sym, sig2, body) => Let(sym, sig2, cont(body))
        case _ => let(sig)(cont)
      }

    val anfMap = new TreeMap {
      def apply[T <: Type](tree: Signal[T]): Signal[T] = tree match {
        case Par(lhs, rhs)          =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Par(lhs2, rhs2)
            }
          }

        case Left(pair)             =>
          anfize(pair) { pair2 =>
            if (pair.eq(pair2)) recur(tree)
            else Left(pair2)
          }

        case Right(pair)            =>
          anfize(pair) { pair2 =>
            if (pair.eq(pair2)) recur(tree)
            else Right(pair2)
          }

        case At(vec, index)         =>
          anfize(vec) { vec2 =>
            if (vec.eq(vec2)) recur(tree)
            else At(vec2, index)
          }

        case Range(vec, to, from)   =>
          anfize(vec) { vec2 =>
            if (vec.eq(vec2)) recur(tree)
            else Range(vec2, to, from).as[T]
          }

        case VecLit(bits)           =>
          tree

        case Var(sym, tpe)          =>
          tree

        case Let(sym, sig, body)    =>
          sig match {
            case Let(sym, sig2, body2) =>
              Let(sym, sig2, Let(sym, body2, body))
            case _ =>  recur(tree)
          }

        case Fsm(sym, init, body)   =>
          val body2 = recur(body)
          if (body.eq(body2)) tree
          else Fsm(sym, init, body2)

        case And(lhs, rhs)          =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else And(lhs2, rhs2)
            }
          }

        case Or(lhs, rhs)           =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Or(lhs2, rhs2)
            }
          }

        case Not(in)                =>
          anfize(in) { in2 =>
            if (in.eq(in2)) recur(tree)
            else Not(in2)
          }

        case Concat(lhs, rhs)     =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Concat(lhs2, rhs2).as[T]
            }
          }

        case Equals(lhs, rhs)     =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Equals(lhs2, rhs2)
            }
          }

        case Plus(lhs, rhs)       =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Plus(lhs2, rhs2)
            }
          }

        case Minus(lhs, rhs)      =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Minus(lhs2, rhs2)
            }
          }

        case Mux(cond, thenp, elsep)  =>
          anfize(cond) { cond2 =>
            anfize(thenp) { thenp2 =>
              anfize(elsep) { elsep2 =>
                if (cond.eq(cond2) && thenp.eq(thenp2) && elsep.eq(elsep2)) recur(tree)
                else Mux(cond2, thenp2, elsep2)
              }
            }
          }

        case Shift(lhs, rhs, isLeft)   =>
          anfize(lhs) { lhs2 =>
            anfize(rhs) { rhs2 =>
              if (lhs.eq(lhs2) && rhs.eq(rhs2)) recur(tree)
              else Shift(lhs2, rhs2, isLeft)
            }
          }
      }
    }

    fix(sig)(anfMap.apply[T])
  }

  def interpret[T <: Type](input: List[Var[_]], body: Signal[T]): List[Value] => Value = {
    def and(lhs: Value, rhs: Value): Value = (lhs, rhs) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        (and(lhs1, lhs2) ~ and(rhs1, rhs2))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        VecV(bits1.zip(bits2).map { case (a, b) => a & b }.asInstanceOf[List[0 | 1]])

      case _ => ??? // impossible
    }

    def or(lhs: Value, rhs: Value): Value = (lhs, rhs) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        (or(lhs1, lhs2) ~ or(rhs1, rhs2))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        VecV(bits1.zip(bits2).map { case (a, b) => a | b }.asInstanceOf[List[0 | 1]])

      case _ => ??? // impossible
    }

    def not(in: Value): Value = (in: @unchecked) match {
      case lhs ~ rhs =>
        (not(lhs) ~ not(rhs))

      case VecV(bits) =>
        VecV(bits.map(i => (i - 1).asInstanceOf[0 | 1]))
    }

    def equals(lhs: Value, rhs: Value): Value = ((lhs, rhs): @unchecked) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        and(equals(lhs1, lhs2), equals(rhs1, rhs2))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        (0 until bits1.size).foldLeft(Value(1)) { (acc, i) =>
          if (bits1(i) == bits2(i)) acc else Value(0)
        }

      // case _ => ??? // impossible
    }

    def plus(lhs: VecV, rhs: VecV): VecV = {
      val size = lhs.size

      assert(lhs.size == rhs.size, "lhs.size = " + lhs.size + ", rhs.size = " + rhs.size)

      val (bits, cout) = (0 until size).foldLeft((Nil, 0): (List[Int], Int)) { case ((bits, cin), i) =>
        val a = lhs(i)
        val b = rhs(i)
        val s = a ^ b ^ cin
        val cout = (a & b) | (cin & (a ^ b))
        (s :: bits, cout)
      }

      VecV(bits.asInstanceOf[List[1 | 0]])
    }

    def minus(lhs: VecV, rhs: VecV): VecV = {
      val size = lhs.size

      assert(lhs.size == rhs.size, "lhs.size = " + lhs.size + ", rhs.size = " + rhs.size)

      val (bits, bout) = (0 until size).foldLeft((Nil, 0): (List[Int], Int)) { case ((bits, bin), i) =>
        val a = lhs(i)
        val b = rhs(i)
        val d = a ^ b ^ bin
        val bout = ((1 - a) & b) | ((1 - a) & bin) | (b & bin)
        (d :: bits, bout)
      }

      VecV(bits.asInstanceOf[List[1 | 0]])
    }

    def shift(lhs: VecV, rhs: VecV, isLeft: Boolean): VecV = {
      val bits: List[Int] = lhs.bits
      val res = (0 until rhs.size).foldLeft(bits) { (acc, i) =>
        val bitsToShift = 1 << i
        val padding = (0 until bitsToShift).map(_ => 0).toList
        val shifted =
          if (isLeft) acc.drop(bitsToShift) ++ padding
          else padding ++ acc.dropRight(bitsToShift)

        if (rhs(i) == 1) shifted
        else acc
      }

      VecV(res.asInstanceOf[List[0 | 1]])
    }

    def recur[T <: Type](sig: Signal[T])(implicit env: Map[Symbol, Value]): Value = { /* println(show(sig)); */ sig} match {
      case Par(lhs, rhs)          =>
        recur(lhs) ~ recur(rhs)

      case Left(pair)             =>
        recur(pair) match {
          case PairV(lhs, rhs) => lhs
          case _ => ??? // imposiible
        }

      case Right(pair)            =>
        recur(pair) match {
          case PairV(lhs, rhs) => rhs
          case _ => ??? // imposiible
        }

      case At(vec, index)         =>
        recur(vec) match {
          case vec: VecV => Value(vec(index))
          case _ => ??? // imposiible
        }

      case Range(vec, to, from)   =>
        recur(vec) match {
          case vec: VecV =>  vec(to, from)
          case _ => ??? // imposiible
        }

      case VecLit(bits)           =>
        VecV(bits)

      case Var(sym, tpe)          =>
        env(sym)

      case Let(sym, sig, body)    =>
        val v = recur(sig)
        recur(body)(env.updated(sym, v))

      case Fsm(sym, init, body)   =>
        ??? // impossible after lifting

      case And(lhs, rhs)          =>
        and(recur(lhs), recur(rhs))

      case Or(lhs, rhs)           =>
        or(recur(lhs), recur(rhs))

      case Not(in)                =>
        not(recur(in))

      case Concat(lhs, rhs)     =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        VecV(lhsV.bits ++ rhsV.bits)

      case Equals(lhs, rhs)     =>
        equals(recur(lhs), recur(rhs))

      case Plus(lhs, rhs)       =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        plus(lhsV, rhsV)

      case Minus(lhs, rhs)      =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        minus(lhsV, rhsV)

      case Mux(cond, thenp, elsep)  =>
        val Value(bitV) = recur(cond)
        if (bitV == 1) recur(thenp)
        else recur(elsep)

      case Shift(lhs, rhs, isLeft)   =>
        val lhsV = recur(lhs).asInstanceOf[VecV]
        val rhsV = recur(rhs).asInstanceOf[VecV]
        shift(lhsV, rhsV, isLeft)
    }

    flatten(lift(body)) match {
      case fsm @ Fsm(sym, init, body) =>
        var lastState = init
        (vs: List[Value]) => {
          val env = input.map(_.sym).zip(vs).toMap + (sym -> lastState)
          // println(env)
          recur(body)(env) match {
            case PairV(lhs, rhs) =>
              lastState = lhs
              // println("out = " + rhs)
              rhs
            case vec: VecV =>  // after detupling
              val sepIndex = fsm.width
              lastState = vec(vec.size - 1, sepIndex)
              vec(sepIndex - 1, 0)
          }
        }

      case code => // combinational
        (vs: List[Value]) => recur(code)(input.map(_.sym).zip(vs).toMap)
    }

  }


  def toVerilog[T <: Type](moduleName: String, input: List[Var[_]], sig: Signal[T]): String = {
    val normailized = optsel(detuple(flatten(lift(sig))))

    import scala.collection.mutable.ListBuffer

    val wires: ListBuffer[String] = ListBuffer.empty
    val assigns: ListBuffer[String] = ListBuffer.empty
    val regs: ListBuffer[String] = ListBuffer.empty

    def template(body: String, sequential: Boolean = false): String = {
      val inputNames = input.map(_.name).mkString(", ")
      val inputDecls = input.map { variable =>
        val hi = detuple(variable).width -  1
        s"input [$hi:0] ${variable.name};"
      }.mkString("\n")

      val outDecl = {
        val hi = normailized.width - 1
        wires += s"wire [$hi:0] out;"
        s"output [$hi:0] out;"
      }

      val clockPort = if (sequential) "CLK, " else ""
      val clockDecl = if (sequential) "input CLK;\n" else ""

      s"module $moduleName ($clockPort $inputNames, out);\n" +
      clockDecl +
      s"$inputDecls\n" +
      s"$outDecl\n" +
      wires.mkString("\n") + "\n" +
      regs.mkString("\n") + "\n\n" +
      assigns.mkString("\n") + "\n\n" +
      s"$body\n" +
      "endmodule\n"
    }

    def letHandler(let: Let[_, _]): String = {
      val name = let.sym.name
      val hi = let.sig.width - 1
      wires += s"wire [$hi:0] $name;"

      val rhs = recur(let.sig)
      assigns += s"assign $name = $rhs;"

      recur(let.body)
    }

    def bits2Verilog(bits: List[Int]): String = {
      val bin = bits.map(_.toString).mkString
      val s = bits.size
      s"$s'b$bin"
    }

    def recur[T <: Type](sig: Signal[T]): String = { /* println(show(sig)); */ sig} match {
      case At(vec, index)         =>
        val vec1 = recur(vec)
        s"$vec1[$index]"

      case Range(vec, to, from)   =>
        val vec1 = recur(vec)
        s"$vec1[$to:$from]"

      case VecLit(bits)           =>
        bits2Verilog(bits)

      case Var(sym, tpe)          =>
        sym.name

      case let @ Let(_, _, _)    =>
        letHandler(let)

      case And(lhs, rhs)          =>
        "( " + recur(lhs) + " & " + recur(rhs) + " )"

      case Or(lhs, rhs)           =>
        "( " + recur(lhs) + " | " + recur(rhs) + " )"

      case Not(in)                =>
        "~" + recur(in)

      case Concat(lhs, rhs)     =>
        "{" + recur(lhs) + ", " + recur(rhs) + " }"

      case Equals(lhs, rhs)     =>
        "( " + recur(lhs) + " == " + recur(rhs) + " )"

      case Plus(lhs, rhs)       =>
        "( " + recur(lhs) + " + " + recur(rhs) + " )"

      case Minus(lhs, rhs)      =>
        "( " + recur(lhs) + " - " + recur(rhs) + " )"

      case Mux(cond, thenp, elsep)  =>
        "( " + recur(cond) + "? " + recur(thenp) + " : " + recur(elsep) + " )"

      case Shift(lhs, rhs, isLeft)   =>
        val op = if (isLeft) "<<" else ">>"

        "( " + recur(lhs) + s" $op " + recur(rhs) + " )"

      case Par(_, _) | Left(_) | Right(_) =>
        ??? // impossible after detupling

      case Fsm(_, _, _)   =>
        ??? // impossible after flattening
    }


    normailized match {
      case fsm @ Fsm(sym, init, body) =>
        val hi = body.width - 1
        val lo = fsm.width
        val hiOut = lo - 1

        val next = recur(body)
        wires += s"wire [$hi:0] next;"
        assigns += s"assign next = $next;"
        assigns += s"assign out = next[$hiOut:0];"

        val stateHi = body.width - fsm.width - 1
        regs += s"reg [$stateHi:0] ${sym.name};"

        val initial = {
          val bin = bits2Verilog(init.asInstanceOf[VecV].bits)
          s"""|initial begin
              |  ${sym.name} = $bin;
              |end\n\n""".stripMargin
        }

        val always = {
          s"""|always @ (posedge CLK)
              |  ${sym.name} <= next[$hi:$lo];\n\n""".stripMargin
        }

        template(initial + always, sequential = true)

      case code => // combinational
        val out = recur(code)
        assigns += s"assign out = $out;"
        template("")
    }
  }

  def simulator[T <: Type](sig: Signal[T]): String = ???

  def tlaplus[T <: Type](sig: Signal[T]): String = ???
}
