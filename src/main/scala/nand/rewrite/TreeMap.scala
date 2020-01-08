package nand
package rewrite

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
