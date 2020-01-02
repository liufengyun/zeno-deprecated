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

      case Range(vec, from, to)   =>
        val vec2 = this(vec)
        if (vec2.eq(vec)) tree
        else Range(vec2, from, to).as[T]

      case VecLit(bits)           =>
        tree

      case Cons(sig, vec)         =>
        val sig2 = this(sig)
        val vec2 = this(vec)
        if (sig2.eq(sig) && vec2.eq(vec)) tree
        else Cons(sig2, vec2).as[T]

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

      case BitLit(value)          =>
        tree

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

        case Range(Fsm(sym, init, body), from, to) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right(from, to)).as[T] } )

        case Equals(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs.as[Vec[0]] === x.right.as[Vec[0]]).as[T] } )

        case Equals(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right.as[Vec[0]] === rhs.as[Vec[0]]).as[T] } )

        case Cons(lhs, Fsm(sym, init, body)) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (lhs :: x.right).as[T] } )

        case Cons(Fsm(sym, init, body), rhs) =>
          Fsm(sym, init, let("x", body) { x => x.left ~ (x.right :: rhs).as[T] } )

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

    var last: Signal[T] = sig
    var current: Signal[T] = liftMap(sig)
    while (current `ne` last) {
      last = current
      current = liftMap(current)
    }

    current
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

  def detuple[T <: Type](sig: Signal[T]): Signal[T] = ???


  def interpret[T <: Type, S <: Type](circuit: Circuit[S, T]): Value[S] => Value[T] = {
    def and[T <: Type](lhs: Value[T], rhs: Value[T]): Value[T] = ???
    def or[T <: Type](lhs: Value[T], rhs: Value[T]): Value[T] = ???
    def not[T <: Type](in: Value[T]): Value[T] = ???
    def equals[T <: Type](lhs: Value[T], rhs: Value[T]): Value[Bit] = ???
    def plus[T <: Num](lhs: Value[Vec[T]], rhs: Value[Vec[T]]): Value[Vec[T]] = ???
    def minus[T <: Num](lhs: Value[Vec[T]], rhs: Value[Vec[T]]): Value[Vec[T]] = ???
    def shift[T <: Num, S <: Num](lhs: Value[Vec[T]], rhs: Value[Vec[S]], isLeft: Boolean): Value[Vec[T]] = ???

    def recur[T <: Type](sig: Signal[T])(implicit env: Map[Symbol, Value[_]]): Value[T] = sig match {
      case Par(lhs, rhs)          =>
        recur(lhs) ~ recur(rhs)

      case Left(pair)             =>
        recur(pair) match {
          case PairV(lhs, rhs) => lhs
        }

      case Right(pair)            =>
        recur(pair) match {
          case PairV(lhs, rhs) => lhs.asInstanceOf
        }

      case At(vec, index)         =>
        recur(vec) match {
          case VecV(map, size) => BitV(map(index))
        }

      case Range(vec, from, to)   =>
        recur(vec) match {
          case VecV(map, size) => VecV(i => map(i + from), to - from).asInstanceOf
        }

      case VecLit(bits)           =>
        VecV(bits, bits.size).asInstanceOf

      case Cons(sig, vec)         =>
        val bitV = recur(sig).asInstanceOf[BitV]
        val vecV = recur(vec).asInstanceOf[VecV[_]]
        VecV(i => if (i == 0) bitV.value else vecV(i - 1), vecV.size + 1).asInstanceOf

      case Var(sym, tpe)          =>
        env(sym).asInstanceOf

      case Let(sym, sig, body)    =>
        val v = recur(sig)
        recur(body)(env.updated(sym, v))

      case Fsm(sym, init, body)   =>
        ??? // impossible after lifting

      case BitLit(value)          =>
        BitV(value)

      case And(lhs, rhs)          =>
        and(recur(lhs), recur(rhs))

      case Or(lhs, rhs)           =>
        or(recur(lhs), recur(rhs))

      case Not(in)                =>
        not(recur(in))

      case Concat(lhs, rhs)     =>
        val lhsV = recur(lhs).asInstanceOf[VecV[_]]
        val rhsV = recur(rhs).asInstanceOf[VecV[_]]
        VecV(i => if (i < lhsV.size) lhsV(i) else rhsV(i - lhsV.size), lhsV.size + rhsV.size).asInstanceOf

      case Equals(lhs, rhs)     =>
        equals(recur(lhs), recur(rhs))

      case Plus(lhs, rhs)       =>
        val lhsV = recur(lhs)
        val rhsV = recur(rhs)
        plus(lhsV, rhsV)

      case Minus(lhs, rhs)      =>
        val lhsV = recur(lhs)
        val rhsV = recur(rhs)
        minus(lhsV, rhsV)

      case Mux(cond, thenp, elsep)  =>
        val bitV: BitV = recur(cond).asInstanceOf[BitV]
        if (bitV.value == 1) recur(thenp)
        else recur(elsep)

      case Shift(lhs, rhs, isLeft)   =>
        val lhsV = recur(lhs)
        val rhsV = recur(rhs)
        shift(lhsV, rhsV, isLeft)
    }

    flatten(lift(circuit.body)) match {
      case Fsm(sym, init, body) =>
        var lastState = init
        (v: Value[S]) => {
          val env = Map(circuit.in.sym -> v, sym -> init)
          recur(body)(env) match {
            case PairV(lhs, rhs) =>
              lastState = lhs
              rhs
          }
        }

      case code => // combinational
        (v: Value[S]) => recur(code)(Map(circuit.in.sym -> v))
    }

  }


  def verilog[T <: Type](sig: Signal[T]): String = ???

  def simulator[T <: Type](sig: Signal[T]): String = ???

  def tlaplus[T <: Type](sig: Signal[T]): String = ???
}
