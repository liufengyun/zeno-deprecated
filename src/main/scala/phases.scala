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


  /** Flatten a lifted tree */
  def flatten[T <: Type](tree: Signal[T]): Signal[T] = tree match {
    case Fsm(sym1, init1, Fsm(sym2, init2, body2)) =>
      fsm(sym1.name + "_" + sym2.name, init1 ~ init2) { state =>
        Let(sym1, state.left,
          Let(sym2, state.right,
            let("x", body2) { x => (x.right.left ~ x.left) ~ x.right.right }
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

    def toVecValue(v: Value[_]): VecV[_] = v match {
      case PairV(lhs, rhs) =>
        (toVecValue(lhs), toVecValue(rhs)) match {
          case (VecV(bits1), VecV(bits2)) => VecV(bits1 ++ bits2)
        }

      case v: VecV[_] =>
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

    val mergeRangeAt = new TreeMap {
      def apply[T <: Type](tree: Signal[T]): Signal[T] = tree match {
        case Range(Range(vec, hi1, lo1), hi2, lo2) =>
          val hi = hi2 + lo1
          val lo = lo2 + lo1
          Range(vec, hi, lo).as[T]

        case At(Range(vec, hi, lo), index) =>
          val index2 = index + lo
          At(vec, index2)

        case _ =>
          recur(tree)
      }
    }

    val sig2 = recur(sig).as[Vec[U]]

    fix(sig2)(mergeRangeAt.apply[Vec[U]])
  }


  def interpret[T <: Type](input: List[Var[_]], body: Signal[T]): List[Value[_]] => Value[T] = {
    def and[T <: Type](lhs: Value[T], rhs: Value[T]): Value[T] = (lhs, rhs) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        (and(lhs1, lhs2.asInstanceOf) ~ and(rhs1, rhs2.asInstanceOf)).asInstanceOf[Value[T]]

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        VecV(bits1.zip(bits2).map { case (a, b) => a & b }.asInstanceOf[List[0 | 1]]).asInstanceOf[Value[T]]

      case _ => ??? // impossible
    }

    def or[T <: Type](lhs: Value[T], rhs: Value[T]): Value[T] = (lhs, rhs) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        (or(lhs1, lhs2.asInstanceOf) ~ or(rhs1, rhs2.asInstanceOf)).asInstanceOf[Value[T]]

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        VecV(bits1.zip(bits2).map { case (a, b) => a | b }.asInstanceOf[List[0 | 1]]).asInstanceOf[Value[T]]

      case _ => ??? // impossible
    }

    def not[T <: Type](in: Value[T]): Value[T] = (in: @unchecked) match {
      case lhs ~ rhs =>
        (not(lhs) ~ not(rhs)).asInstanceOf[Value[T]]

      case VecV(bits) =>
        VecV(bits.map(i => (i - 1).asInstanceOf[0 | 1])).asInstanceOf[Value[T]]
    }

    def equals[T <: Type](lhs: Value[T], rhs: Value[T]): Value[Bit] = ((lhs, rhs): @unchecked) match {
      case (lhs1 ~ rhs1, lhs2 ~ rhs2) =>
        and(equals(lhs1, lhs2.asInstanceOf), equals(rhs1, rhs2.asInstanceOf))

      case (VecV(bits1), VecV(bits2)) if bits1.size == bits2.size =>
        (0 until bits1.size).foldLeft(Bits(1)) { (acc, i) =>
          if (bits1(i) == bits2(i)) acc else Bits(0)
        }.asInstanceOf[Value[Bit]]

      // case _ => ??? // impossible
    }

    def plus[T <: Num](lhs: VecV[T], rhs: VecV[T]): VecV[T] = {
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

    def minus[T <: Num](lhs: VecV[T], rhs: VecV[T]): VecV[T] = {
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

    def shift[T <: Num, S <: Num](lhs: VecV[T], rhs: VecV[S], isLeft: Boolean): VecV[T] = {
      val bits: List[Int] = (0 until lhs.size).map(lhs(_)).toList
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

    def recur[T <: Type](sig: Signal[T])(implicit env: Map[Symbol, Value[_]]): Value[T] = { /* println(show(sig)); */ sig} match {
      case Par(lhs, rhs)          =>
        recur(lhs) ~ recur(rhs)

      case Left(pair)             =>
        recur(pair) match {
          case PairV(lhs, rhs) => lhs
        }

      case Right(pair)            =>
        recur(pair) match {
          case PairV(lhs, rhs) => rhs
        }

      case At(vec, index)         =>
        recur(vec) match {
          case vec: VecV[_] => Bits(vec(index)).asInstanceOf[Value[T]]
        }

      case Range(vec, to, from)   =>
        recur(vec) match {
          case vec: VecV[_] =>  vec(to, from).asInstanceOf[Value[T]]
        }

      case VecLit(bits)           =>
        VecV(bits).asInstanceOf[Value[T]]

      case Var(sym, tpe)          =>
        env(sym).asInstanceOf[Value[T]]

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
        val lhsV = recur(lhs).asInstanceOf[VecV[_]]
        val rhsV = recur(rhs).asInstanceOf[VecV[_]]
        VecV(lhsV.bits ++ rhsV.bits).asInstanceOf[Value[T]]

      case Equals(lhs, rhs)     =>
        equals(recur(lhs), recur(rhs))

      case Plus(lhs, rhs)       =>
        val lhsV = recur(lhs)
        val rhsV = recur(rhs)
        plus(lhsV.asInstanceOf, rhsV.asInstanceOf).asInstanceOf[Value[T]]

      case Minus(lhs, rhs)      =>
        val lhsV = recur(lhs)
        val rhsV = recur(rhs)
        minus(lhsV.asInstanceOf, rhsV.asInstanceOf).asInstanceOf[Value[T]]

      case Mux(cond, thenp, elsep)  =>
        val Bits(bitV) = recur(cond)
        if (bitV == 1) recur(thenp)
        else recur(elsep)

      case Shift(lhs, rhs, isLeft)   =>
        val lhsV = recur(lhs)
        val rhsV = recur(rhs)
        shift(lhsV.asInstanceOf, rhsV.asInstanceOf, isLeft).asInstanceOf[Value[T]]
    }

    flatten(lift(body)) match {
      case fsm @ Fsm(sym, init, body) =>
        var lastState = init
        (vs: List[Value[_]]) => {
          val env = input.map(_.sym).zip(vs).toMap + (sym -> lastState)
          // println(env)
          recur(body)(env) match {
            case PairV(lhs, rhs) =>
              lastState = lhs
              // println("out = " + rhs)
              rhs
            case vec: VecV[_] =>  // after detupling
              val sepIndex = fsm.tpe.asInstanceOf[Vec[_]].size
              lastState = vec(vec.size - 1, sepIndex).asInstanceOf
              vec(sepIndex - 1, 0).asInstanceOf[Value[T]]
          }
        }

      case code => // combinational
        (vs: List[Value[_]]) => recur(code)(input.map(_.sym).zip(vs).toMap)
    }

  }


  def verilog[T <: Type](sig: Signal[T]): String = ???

  def simulator[T <: Type](sig: Signal[T]): String = ???

  def tlaplus[T <: Type](sig: Signal[T]): String = ???
}
