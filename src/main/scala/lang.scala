package ysm

import scala.language.implicitConversions
import scala.compiletime._

object lang {
  /** Representation of circuit
   *
   *  Final tagless is avoied for two reasons:
   *  - usability with path-dependent types is not good
   *  - it's reported in Lava that AST representation is better for processing
   */

  // ---------------- Type of signal --------------------

  sealed abstract class Type
  case class Pair[S <: Type, T <: Type](lhs: S, rhs: T) extends Type
  case class Vec[T <: Num](size: T) extends Type

  type ~[S <: Type, T <: Type] = Pair[S, T]
  type Bit = Vec[1]
  type Num = Int & Singleton

  // ---------------- values of signal --------------------

  sealed abstract class Value

  case class PairV(lhs: Value, rhs: Value) extends Value

  case class VecV(bits: List[0 | 1]) extends Value {
    // bits are stored in reverse order
    def apply(i: Int): 0 | 1 = bits(size - i - 1)
    def size: Int = bits.size
    def apply(to: Int, from: Int): VecV =
      VecV(bits.dropRight(from).drop(bits.size - to - 1))
  }

  object Value {
    def apply(bit: 0 | 1, bits: (0 | 1)*): Value =
      new VecV(bit :: bits.toList)

    def unapplySeq[T <: Type](value: Value): Option[List[0 | 1]] = value match {
      case VecV(bits) => Some(bits)
      case _ => None
    }
  }

  def (vec: Value) toInt: Int = vec match {
    case vec: VecV =>
      (0 until vec.size).foldLeft(0) { (acc, i) => acc | ((vec(i) & 1) << i) }

    case _ =>
      throw new Exception("Cannot call .toInt on pairs")
  }

  def [T <: Num](value: Value) toShort: Short = value.toInt.toShort

  def [T <: Num](value: Value) toChar: Int = value.toInt.toChar

  // ---------------- abstract syntax trees --------------------

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

  // TODO: T should be covariant to support `Signal[Vec[5]] <: Signal[Vec[_]]`
  //       Currently, Dotty crashes with the change.
  sealed abstract class Signal[T <: Type] {
    count += 1

    def ~[U <: Type](rhs: Signal[U]): Signal[T ~ U] = Par(this, rhs)

    def as[S <: Type]: Signal[S] = {
      this.asInstanceOf[Signal[S]]
    }

    def asPair[S <: Type, U <: Type]: Signal[S ~ U] = {
      // TODO: add dynamic check
      this.as[S ~ U]
    }

    def width: Int = tpe match {
      case vec: Vec[_] => vec.size
      case _ => throw new Exception("access size on non-vector signal")
    }


    def tpe: Type
  }

  case class Par[S <: Type, T <: Type](lhs: Signal[S], rhs: Signal[T]) extends Signal[S ~ T] {
    val tpe: Type = new Pair(lhs.tpe, rhs.tpe)
  }

  case class Left[S <: Type, T <: Type](pair: Signal[S ~ T]) extends Signal[S] {
    val tpe: Type = pair.tpe match {
      case Pair(t1, t2) => t1
      case _ => ???  // impossible
    }
  }

  case class Right[S <: Type, T <: Type](pair: Signal[S ~ T]) extends Signal[T] {
    val tpe: Type = pair.tpe match {
      case Pair(t1, t2) => t2
      case _ => ???  // impossible
    }
  }

  case class At[T <: Num](vec: Signal[Vec[T]], index: Int) extends Signal[Bit] {
    assert(index < vec.size, "vec.size = " + vec.size + ", index = " + index)

    val tpe: Type = Vec(1)
  }

  case class Range[T <: Num, S <: Num](vec: Signal[Vec[T]], to: Int, from: Int) extends Signal[Vec[S]] {
    private def debug: String = s"$to..$from, vec.size = ${vec.size}"
    assert(from < vec.size && from >= 0, debug)
    assert(to < vec.size && from >= 0, debug)
    assert(from <= to, debug)

    val tpe: Type = {
      val size = to - from + 1
      Vec(size)
    }
  }

  /** vector literal */
  case class VecLit[T <: Num](bits: List[0 | 1]) extends Signal[Vec[T]] {
    val tpe: Type = {
      val size = bits.size
      Vec(size)
    }
  }

  case class Var[T <: Type](sym: Symbol, tpe: Type) extends Signal[T] {
    val name: String = sym.name
  }

  case class Let[S <: Type, T <: Type](sym: Symbol, sig: Signal[S],  body: Signal[T]) extends Signal[T] {
    val tpe: Type = body.tpe
  }

  case class Fsm[S <: Type, T <: Type](sym: Symbol, init: Value, body: Signal[S ~ T]) extends Signal[T] {
    val tpe: Type = body.tpe match {
      case Pair(t1, t2) => t2
      case Vec(size) =>
        // after detupling
        val initV = init.asInstanceOf[VecV]
        val outSize = size - initV.size
        Vec(outSize)
    }
  }

  case class And[T <: Type](lhs: Signal[T], rhs: Signal[T]) extends Signal[T] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)
    val tpe: Type = lhs.tpe
  }

  case class Or[T <: Type](lhs: Signal[T], rhs: Signal[T]) extends Signal[T] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)
    val tpe: Type = lhs.tpe
  }

  case class Not[T <: Type](in: Signal[T]) extends Signal[T] {
    val tpe: Type = in.tpe
  }

  /** vec1 ++ vec2. Used to reduce program size */
  case class Concat[S <: Num, T <: Num, U <: Num](vec1: Signal[Vec[S]], vec2: Signal[Vec[T]]) extends Signal[Vec[U]] {
    val tpe: Type = {
      val size = vec1.size + vec2.size
      Vec(size)
    }
  }

  /** vec1 === vec2. Used to reduce program size */
  case class Equals[T <: Type](lhs: Signal[T], rhs: Signal[T]) extends Signal[Bit] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)
    val tpe: Type = Vec(1)
  }

  /** vec1 + vec2. Used to reduce program size */
  case class Plus[T <: Num](lhs: Signal[Vec[T]], rhs: Signal[Vec[T]]) extends Signal[Vec[T]] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)

    val tpe: Type = lhs.tpe
  }

  /** vec1 + vec2. Used to reduce program size */
  case class Minus[T <: Num](lhs: Signal[Vec[T]], rhs: Signal[Vec[T]]) extends Signal[Vec[T]] {
    assert(lhs.tpe == rhs.tpe, "lhs.tpe = " + lhs.tpe + ", rhs.tpe = " + rhs.tpe)

    val tpe: Type = lhs.tpe
  }

  /** if (c) x else y. Used to reduce program size  */
  case class Mux[T <: Type](cond: Signal[Bit], thenp: Signal[T], elsep: Signal[T]) extends Signal[T] {
    assert(thenp.tpe == elsep.tpe, "thenp.tpe = " + thenp.tpe + ", elsep.tpe = " + elsep.tpe)

    val tpe: Type = thenp.tpe
  }

  /** x << y and x >> y. Used to reduce program size  */
  case class Shift[S <: Num, T <: Num](vec: Signal[Vec[S]], amount: Signal[Vec[T]], isLeft: Boolean) extends Signal[Vec[S]] {
    val tpe: Type = vec.tpe
  }

  // ---------------- type operations --------------------

  inline def typeOf[T <: Type]: T = inline erasedValue[T] match {
    case _: ~[t1, t2]  =>
      (new Pair(typeOf[t1], typeOf[t2])).asInstanceOf

    case _: Vec[n]     =>
      val size = valueOf[n]
      Vec(size).asInstanceOf
  }

  def typeOf(value: Value): Type = value match {
    case PairV(l, r)  =>
      new ~(typeOf(l), typeOf(r))

    case VecV(bits)   =>
      val size = bits.size
      Vec(size)
  }

  // ---------------- constructors --------------------

  def let[S <: Type, T <: Type](name: String, t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] = {
    val sym = Symbol.fresh(name)
    Let(sym, t, fn(Var(sym, t.tpe)))
  }

  def let[S <: Type, T <: Type](t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] =
    let("x", t)(fn)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) left: Signal[S] = Left(t)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) right: Signal[T] = Right(t)

  object ~ {
    def unapply[S <: Type, T <: Type](sig: Signal[S ~ T]): (Signal[S], Signal[T]) =
      (sig.left, sig.right)

    def unapply(value: Value): Option[(Value, Value)] = value match {
      case PairV(lhs, rhs) => Some((lhs, rhs))
      case _ => None
    }
  }

  def fsm[S <: Type, T <: Type](name: String, init: Value)(next: Signal[S] => Signal[S ~ T]): Signal[T] = {
    val tpInit = typeOf(init)
    val sym = Symbol.fresh(name)
    val body = next(Var(sym, tpInit))

    body.tpe match {
      case Pair(s, t) =>
        if (s != tpInit) throw new Exception("incorrect type of FSM body. Expected = " + tpInit + ", found = " + s)

      case tp =>
        throw new Exception("unexpected type of FSM body. Pair type expected " + ", found = " + tp)
    }

    Fsm(sym, init, body)
  }

  def mux[T <: Type](cond: Signal[Bit], x: Signal[T], y: Signal[T]): Signal[T] = Mux(cond, x, y)

  def [T <: Type](sig: Signal[T]) unary_! : Signal[T] = Not(sig)

  def [T <: Type](lhs: Signal[T]) & (rhs: Signal[T]): Signal[T] = And(lhs, rhs)

  def [T <: Type](lhs: Signal[T]) | (rhs: Signal[T]): Signal[T] = Or(lhs, rhs)

  def [T <: Type](lhs: Signal[T]) ^ (rhs: Signal[T]): Signal[T] = Or(And(lhs, !rhs), And(!lhs, rhs))

  def [T <: Type](value: Value) toSignal: Signal[T] = value match {
    case PairV(l, r) =>
      (l.toSignal ~ r.toSignal).asInstanceOf

    case VecV(bits)  =>
      VecLit(bits).asInstanceOf
  }

  inline def variable[T <: Type](name: String): Var[T] =
    Var(Symbol(name), typeOf[T])

  def (lhs: Value) ~ (rhs: Value): Value =
    new PairV(lhs, rhs)

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Signal[Bit]] = b => Vec(if b then 1 else 0)
  implicit val lit1: Conversion[1, Signal[Bit]] = one => Vec(1)
  implicit val lit0: Conversion[0, Signal[Bit]] = zero => Vec(0)

  /** Int -> Bits */
  def (n: Int) toValue(N: Int): Value = {
    assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
    assert(n >= 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

    val bits = (0 until N).foldLeft(Nil: List[0|1]) { (acc, i) =>
      val bit: 0 | 1 = if (n & (1 << i)) == 0 then 0 else 1
      bit :: acc
    }

    VecV(bits)
  }

  /** Int -> Bits, take the least significant N bits */
  def [N <: Num](n: Int) W(implicit M: ValueOf[N]): Signal[Vec[N]] = {
    val N = M.value.asInstanceOf[Int]
    val bits = (0 until N).foldLeft(Nil: List[0|1]) { (acc, i) =>
      val bit: 0 | 1 = if (n & (1 << i)) == 0 then 0 else 1
      bit :: acc
    }
    VecLit(bits)
  }

  // ---------------- bit vector operations --------------------

  def [M <: Num, N <: Num](vec: Signal[Vec[M]]) << (amount: Signal[Vec[N]]): Signal[Vec[M]] =
    Shift(vec, amount, isLeft = true)

  def [M <: Num, N <: Num](vec: Signal[Vec[M]]) >> (amount: Signal[Vec[N]]): Signal[Vec[M]] =
    Shift(vec, amount, isLeft = false)

  def [N <: Num](lhs: Signal[Vec[N]]) + (rhs: Signal[Vec[N]]): Signal[Vec[N]] =
    Plus(lhs, rhs)

  def [N <: Num](lhs: Signal[Vec[N]]) - (rhs: Signal[Vec[N]]): Signal[Vec[N]] =
    Minus(lhs, rhs)

  def Vec[T <: Num](bit: 1 | 0, bits: (1 | 0)*): Signal[Vec[T]] =
    VecLit[T](bit :: bits.toList)

  def Vec[T <: Num](bits: Signal[Bit]*): Signal[Vec[T]] =
    bits.foldRight(VecLit[T](Nil).as[Vec[T]]) { (bit, acc) =>
      bit ++ acc
    }

  def [M <: Num, N <: Num, U <: Num](lhs: Signal[Vec[M]]) ++ (rhs: Signal[Vec[N]]): Signal[Vec[U]] = Concat(lhs, rhs)

  def [S <: Num](vec: Signal[Vec[S]]) apply(index: Int): Signal[Bit] = At(vec, index)

  def [S <: Num, U <: Num](vec: Signal[Vec[S]]) apply(to: Int, from: Int): Signal[Vec[U]] = Range[S, U](vec, to, from)

  def [T <: Num](x: Signal[Vec[T]]) === (y: Signal[Vec[T]]): Signal[Bit] = Equals(x, y)

  def [N <: Num](vec: Signal[Vec[N]]) size: Int = vec.tpe.asInstanceOf[Vec[N]].size

  private  def shiftImpl[M <: Num, N <: Num](vec: Signal[Vec[N]], amount: Signal[Vec[M]], isLeft: Boolean): Signal[Vec[N]] = {
    val n: Int = vec.size
    val m: Int = amount.size

    // index starts from least significant bit of `amount`
    def recur(index: Int, toShift: Signal[Vec[N]]): Signal[Vec[N]] =
      if (index >= m) toShift
      else {
        val bitsToShift = 1 << index
        val padding = 0.W[bitsToShift.type]
        val shifted: Signal[Vec[N]] =
          if (isLeft) (toShift(bitsToShift, n - 1) ++ padding).as[Vec[N]]
          else (padding ++ toShift(0, n - bitsToShift - 1)).as[Vec[N]]

        val test =
          when (amount(index)) {
            shifted
          } otherwise {
            toShift
          }
        recur(index + 1, test)
      }

    recur(0, vec)
  }


  /** logical shift left */
  def shiftLeft[M <: Num, N <: Num](vec: Signal[Vec[M]], amount: Signal[Vec[N]]): Signal[Vec[M]] =
    shiftImpl(vec, amount, isLeft = true)

  /** logical shift  right */
  def shiftRight[M <: Num, N <: Num](vec: Signal[Vec[M]], amount: Signal[Vec[N]]): Signal[Vec[M]] =
    shiftImpl(vec, amount, isLeft = false)

  /** unsigned addition, ripple-carry adder */
  def plus[N <: Num](vec1: Signal[Vec[N]], vec2: Signal[Vec[N]]): Signal[Vec[N]] = {
    val n: Int = vec1.size

    // index starts from least significant bit
    def recur(index: Int, cin: Signal[Bit], acc: Signal[Vec[_]]): (Signal[Bit], Signal[Vec[N]]) =
      if (index >= n) (cin, acc.as[Vec[N]])
      else {
        val a: Signal[Bit] = vec1(index)
        val b: Signal[Bit] = vec2(index)
        val s: Signal[Bit] = a ^ b ^ cin
        val cout: Signal[Bit] = (a & b ) | (cin & (a ^ b))
        recur(index + 1, cout, (s ++ acc.as[Vec[N]]).asInstanceOf)
      }

    recur(0, lit(false), Vec().as[Vec[_]])._2
  }

  /** unsigned subtraction */
  def minus[N <: Num](vec1: Signal[Vec[N]], vec2: Signal[Vec[N]]): Signal[Vec[N]] = {
    val n: Int = vec1.size

    // index starts from least significant bit
    def recur(index: Int, bin: Signal[Bit], acc: Signal[Vec[_]]): (Signal[Bit], Signal[Vec[N]]) =
      if (index >= n) (bin, acc.as[Vec[N]])
      else {
        val a: Signal[Bit] = vec1(index)
        val b: Signal[Bit] = vec2(index)
        val d: Signal[Bit] = a ^ b ^ bin
        val bout: Signal[Bit] = (!a & b) | (!a & bin) | (b & bin)
        recur(index + 1, bout, (d ++ acc.as[Vec[N]]).as[Vec[_]])
      }

    recur(0, lit(false), Vec().as[Vec[_]])._2
  }

  /** Concat two bit vectors */
  def concat[M <: Num, N <: Num, U <: Num](sig1: Signal[Vec[M]], sig2: Signal[Vec[N]]): Signal[Vec[U]] = {
    def recur(index: Int): Signal[Vec[N]] =
      if (index == 0) sig1(0) ++ sig2
      else sig1(index) ++ recur(index - 1)

    if (sig1.size == 0) sig2.as[Vec[U]]
    else recur(sig1.size - 1).as[Vec[U]]
  }

  def equalsBit(x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (x & y) | (!x & !y)
  def equals[T <: Type](x: Signal[T], y: Signal[T]): Signal[Bit] =  x.tpe match {
    case Pair(t1, t2) =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.as[T1 ~ T2]
      val y1 = y.as[T1 ~ T2]
      equals(x1.left, y1.left) & equals(x1.right, y1.right)

    case Vec(n) =>
      (0 until n).map { i =>
        equalsBit(x.as[Vec[n.type]](i), y.as[Vec[n.type]](i))
      }.reduce(_ & _)
  }

  // ----------------  utilities --------------------

  // Tuple -> Pair
  implicit def tuple2toPair[S <: Type, T <: Type]: Conversion[(Signal[S], Signal[T]), Signal[S ~ T]] =
    t2 => t2._1 ~ t2._2

  implicit def tuple3toPair[T1 <: Type, T2 <: Type, T3 <: Type]: Conversion[(Signal[T1], Signal[T2], Signal[T3]), Signal[T1 ~ T2 ~ T3]] =
    t3 => t3._1 ~ t3._2 ~ t3._3

  def test1(cond: Signal[Bit], x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (!cond | x) & (cond | y)
  def test[T <: Type](cond: Signal[Bit], x: Signal[T], y: Signal[T]): Signal[T] = x.tpe match {
    case Pair(t1, t2) =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.as[T1 ~ T2]
      val y1 = y.as[T1 ~ T2]
      (mux(cond, x1.left, y1.left) ~ mux(cond, x1.right, y1.right)).as[T]

    case Vec(n) =>
      val xSize = x.as[Vec[0]].size
      val ySize = y.as[Vec[0]].size
      assert(xSize == ySize, "x.size = " +  xSize + ", y.size = " +  ySize)

      (0 until n).foldLeft(Vec()) { (acc, i) =>
        test1(cond, x.as[Vec[n.type]](i), y.as[Vec[n.type]](i)) ++ acc
      }.as[T]
  }

  /** When syntax
   *
   *  when (a) {
   *
   *  } when (b) {
   *
   *  } otherwise {
   *
   *  }
   */
  def when[T <: Type](cond: Signal[Bit])(x: Signal[T]): WhenCont[T] =
    WhenCont { r => mux(cond, x, r) }
  class WhenCont[T <: Type](cont: Signal[T] => Signal[T]) {
    def otherwise(y: Signal[T]): Signal[T] = cont(y)

    def when (cond2: Signal[Bit])(y: Signal[T]): WhenCont[T] =
      WhenCont { r => cont(mux(cond2, y, r)) }
  }

  // ---------------- pretty print --------------------

  def show[T <: Type](sig: Signal[T]): String = {
    var indent = 0

    def padding: String = "\n" + ("  " * indent)

    def indented(str: => String): String = indentedWith(tabs = 1)(str)

    def indentedWith(tabs: Int)(str: => String): String = {
      indent += 1
      val res = str
      indent -= 1
      res
    }

    def recur[T <: Type](sig: Signal[T]): String =
      sig match {
        case Par(lhs, rhs) => recur(lhs) + " ~ " + recur(rhs)

        case Left(pair)    => recur(pair) + ".1"

        case Right(pair)   => recur(pair) + ".2"

        case At(vec, i)    => recur(vec) + "(" + i + ")"

        case Range(vec, to, from) =>
          recur(vec) + "(" + to + ".." + from + ")"

        case VecLit(Nil)   =>
          "Vec()"

        case VecLit(bits)   =>
          if (bits.size <= 4) bits.map(_.toString).mkString
          else toHex(bits)

        case Concat(vec1, vec2) =>
          recur(vec1) + " ++ " + recur(vec2)

        case Var(sym, tpe)  =>
          sym.name

        case Let(sym, sig, body) =>
          indented {
            padding + "let " + sym.name + ": " + show(sig.tpe)  +  " = " + recur(sig) +
            padding + "in" +
            padding + indented { recur(body) }
          }

        case Fsm(sym, init, body) =>
          indented {
            padding + "fsm { " + show(init) + " | " + sym.name + " => " +
            indentedWith(tabs = 2) { padding + recur(body) } +
            padding + "}"
          }

        case Equals(vec1, vec2) =>
          recur(vec1) + "===" + recur(vec2)

        case Plus(vec1, vec2) =>
          recur(vec1) + " + " + recur(vec2)

        case Minus(vec1, vec2) =>
          recur(vec1) + " - " + recur(vec2)

        case Shift(vec, amount, isLeft) =>
          val dir = if (isLeft) " << " else " >> "
          recur(vec) + dir + recur(amount)

        case Mux(cond, vec1, vec2) =>
          indented {
            padding + "if (" + recur(cond) + ") " + recur(vec1) +
            padding + "else " + recur(vec2)
          }

        case And(lhs, rhs)  =>
          recur(lhs) + " & " + recur(rhs)

        case Or(lhs, rhs)   =>
          recur(lhs) + " | " + recur(rhs)

        case Not(in)        =>
          "!" + recur(in)
      }

    recur(sig)
  }

  def show(tpe: Type): String = tpe match {
    case Pair(t1, t2) => show(t1) + " ~ " + show(t2)
    case Vec(size)    => "Vec[" + size + "]"
  }

  def show(value: Value): String = value match {
    case PairV(l, r)     => show(l) + " ~ " + show(r)
    case VecV(bits)      =>
      if (bits.size <= 4) bits.map(_.toString).mkString else toHex(bits)
  }

  def toHex(bits: List[0 | 1]): String = {
    var base: Int = 1
    var sum: Int = 0
    var count: Int = 0
    val sb = new StringBuilder
    bits.foldRight(sb) { (bit, sbt) =>
      count += 1
      sum += bit * base
      base *= 2

      if (base > 8 || count == bits.size) {
        base = 1

        if(sum < 10) sb.insert(0, sum.toString)
        else if(sum == 10) sb.insert(0, "A")
        else if(sum == 11) sb.insert(0, "B")
        else if(sum == 12) sb.insert(0, "C")
        else if(sum == 13) sb.insert(0, "D")
        else if(sum == 14) sb.insert(0, "E")
        else if(sum == 15) sb.insert(0, "F")

        sum = 0
      }

      sb
    }

    sb.toString
  }
}
