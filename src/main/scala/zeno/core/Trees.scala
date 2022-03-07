package zeno.core

import Types._, Values._

/** Representation of circuit in typed AST
  *
  *  Final tagless is avoied for two reasons:
  *  - usability with path-dependent types is not good
  *  - it's reported in Lava that AST representation is better for processing
  */

// TODO: T should be covariant to support `Sig[Vec[5]] <: Sig[Vec[_]]`
//       Currently, Dotty crashes with the change.
sealed abstract class Sig[T <: Type] {
  Trees.count += 1
  val id = Trees.count

  private[zeno] def as[S <: Type]: Sig[S] = {
    this.asInstanceOf[Sig[S]]
  }

  def tpe: Type

  private[zeno] def width: Int = this.tpe.asInstanceOf[Vec[_]].width
}

private[zeno] object Trees {
  // symbol for bindings
  case class Symbol(name: String)

  object Symbol {
    import collection.mutable.Map
    private val map: Map[String, Int] = Map.empty
    def fresh(name: String): Symbol = {
      if (map.contains(name)) {
        val count = map(name)
        map(name) = count + 1
        Symbol(name + count)
      }
      else {
        map(name) = 1
        Symbol(name)
      }
    }
  }

  var count = 0

  case class Pair[S <: Type, T <: Type](lhs: Sig[S], rhs: Sig[T]) extends Sig[S ~ T] {
    val tpe: Type = new PairT(lhs.tpe, rhs.tpe)
  }

  case class Left[S <: Type, T <: Type](pair: Sig[S ~ T]) extends Sig[S] {
    val tpe: Type = pair.tpe match {
      case PairT(t1, t2) => t1
      case _ => ???  // impossible
    }
  }

  case class Right[S <: Type, T <: Type](pair: Sig[S ~ T]) extends Sig[T] {
    val tpe: Type = pair.tpe match {
      case PairT(t1, t2) => t2
      case _ => ???  // impossible
    }
  }

  case class At[T <: Num](vec: Sig[Vec[T]], index: Int) extends Sig[Bit] {
    assert(index < vec.width, "vec.width = " + vec.width + ", index = " + index)

    val tpe: Type = VecT(1)
  }

  case class Range[T <: Num, S <: Num](vec: Sig[Vec[T]], to: Int, from: Int) extends Sig[Vec[S]] {
    private def debug: String = s"$to..$from, vec.width = ${vec.width}"
    assert(from < vec.width && from >= 0, debug)
    assert(to < vec.width && from >= 0, debug)
    assert(from <= to, debug)

    val tpe: Type = {
      val width = to - from + 1
      VecT(width)
    }
  }

  /** vector literal */
  case class VecLit[T <: Num](bits: List[0 | 1]) extends Sig[Vec[T]] {
    val tpe: Type = {
      val width = bits.size
      VecT(width)
    }
  }

  case class Var[T <: Type](sym: Symbol, tpe: Type) extends Sig[T] {
    val name: String = sym.name
  }

  case class Let[S <: Type, T <: Type](sym: Symbol, sig: Sig[S],  body: Sig[T]) extends Sig[T] {
    val tpe: Type = body.tpe
  }

  case class Fsm[S <: Type, T <: Type](sym: Symbol, init: Value, body: Sig[S ~ T]) extends Sig[T] {
    val tpe: Type = body.tpe match {
      case PairT(t1, t2) => t2
      case VecT(width) =>
        // after detupling
        val initV = init.asInstanceOf[VecV]
        val outSize = width - initV.width
        VecT(outSize)
    }
  }

  case class And[T <: Num](lhs: Sig[Vec[T]], rhs: Sig[Vec[T]]) extends Sig[Vec[T]] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)
    val tpe: Type = lhs.tpe
  }

  case class Or[T <: Num](lhs: Sig[Vec[T]], rhs: Sig[Vec[T]]) extends Sig[Vec[T]] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)
    val tpe: Type = lhs.tpe
  }

  case class Not[T <: Num](in: Sig[Vec[T]]) extends Sig[Vec[T]] {
    val tpe: Type = in.tpe
  }

  /** vec1 ++ vec2 */
  case class Concat[S <: Num, T <: Num, U <: Num](vec1: Sig[Vec[S]], vec2: Sig[Vec[T]]) extends Sig[Vec[U]] {
    val tpe: Type = {
      val width = vec1.width + vec2.width
      VecT(width)
    }
  }

  /** vec1 === vec2 */
  case class Equals[T <: Num](lhs: Sig[Vec[T]], rhs: Sig[Vec[T]]) extends Sig[Bit] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)
    val tpe: Type = VecT(1)
  }

  /** vec1 + vec2 */
  case class Plus[T <: Num](lhs: Sig[Vec[T]], rhs: Sig[Vec[T]]) extends Sig[Vec[T]] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)

    val tpe: Type = lhs.tpe
  }

  /** vec1 + vec2 */
  case class Minus[T <: Num](lhs: Sig[Vec[T]], rhs: Sig[Vec[T]]) extends Sig[Vec[T]] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)

    val tpe: Type = lhs.tpe
  }

  /** if (c) x else y */
  case class Mux[T <: Type](cond: Sig[Bit], thenp: Sig[T], elsep: Sig[T]) extends Sig[T] {
    assert(thenp.tpe == elsep.tpe, "thenp.tpe = " + thenp.tpe + ", elsep.tpe = " + elsep.tpe)

    val tpe: Type = thenp.tpe
  }

  /** x << y and x >> y */
  case class Shift[S <: Num, T <: Num](vec: Sig[Vec[S]], amount: Sig[Vec[T]], isLeft: Boolean) extends Sig[Vec[S]] {
    val tpe: Type = vec.tpe
  }
}