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
  object Bit extends Type
  case class Pair[S <: Type, T <: Type](lhs: S, rhs: T) extends Type
  case class Vec[T <: Num](size: T) extends Type

  type ~[S <: Type, T <: Type] = Pair[S, T]
  type Bit = Bit.type
  type Num = Int & Singleton

  // ---------------- values of signal --------------------

  sealed abstract class Value[T <: Type]

  case class BitV(value: 0 | 1) extends Value[Bit]

  case class PairV[S <: Type, T <: Type](lhs: Value[S], rhs: Value[T]) extends Value[S ~ T]

  case class VecV[T <: Num](map: Int => 0 | 1, size: Int) extends Value[Vec[T]] {
    def apply(i: Int): 0 | 1 = map(i)
  }

  def [T <: Num](value: Value[Bit] | Value[Vec[T]]) toInt: Int = value match {
    case BitV(value) => value
    case VecV(map, size) =>
      (0 until size).foldLeft(0) { (acc, i) => acc | (map(i) & 1) << i }
  }

  def [T <: Num](value: Value[Bit] | Value[Vec[T]]) toShort: Short = value.toInt.toShort

  def [T <: Num](value: Value[Vec[T]]) toChar: Int = value.toInt.toChar

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

  sealed abstract class Signal[T <: Type] {
    count += 1

    def ~[U <: Type](rhs: Signal[U]): Signal[T ~ U] = Par(this, rhs)

    def as[S <: Type]: Signal[S] = {
      // TODO: add dynamic check
      this.asInstanceOf[Signal[S]]
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

    val tpe: Type = Bit
  }

  case class Range[T <: Num, S <: Num](vec: Signal[Vec[T]], from: Int, to: Int) extends Signal[Vec[S]] {
    private def debug: String = "from = " + from + ", to = " + to + ", vec.size = " + vec.size
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

  case class Cons[T <: Num, U <: Num](sig: Signal[Bit], vec: Signal[Vec[T]]) extends Signal[Vec[U]] {
    val tpe: Type = {
      val size = vec.size + 1
      Vec(size)
    }
  }

  case class Var[T <: Type](sym: Symbol, tpe: Type) extends Signal[T]

  case class Let[S <: Type, T <: Type](sym: Symbol, sig: Signal[S],  body: Signal[T]) extends Signal[T] {
    val tpe: Type = body.tpe
  }

  case class Fsm[S <: Type, T <: Type](sym: Symbol, init: Value[S], body: Signal[S ~ T]) extends Signal[T] {
    val tpe: Type = body.tpe match {
      case Pair(t1, t2) => t2
      case _ => ???  // impossible
    }
  }

  case class BitLit(value: 0 | 1) extends Signal[Bit] {
    val tpe: Type = Bit
  }

  case class And[T <: Type](lhs: Signal[T], rhs: Signal[T]) extends Signal[T] {
    assert(lhs.tpe == rhs.tpe)
    val tpe: Type = lhs.tpe
  }

  case class Or[T <: Type](lhs: Signal[T], rhs: Signal[T]) extends Signal[T] {
    assert(lhs.tpe == rhs.tpe)
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
  case class Equals[T <: Type](vec1: Signal[T], vec2: Signal[T]) extends Signal[Bit] {
    val tpe: Type = Bit
  }

  /** vec1 + vec2. Used to reduce program size */
  case class Plus[T <: Num](vec1: Signal[Vec[T]], vec2: Signal[Vec[T]]) extends Signal[Vec[T]] {
    val tpe: Type = vec1.tpe
  }

  /** vec1 + vec2. Used to reduce program size */
  case class Minus[T <: Num](vec1: Signal[Vec[T]], vec2: Signal[Vec[T]]) extends Signal[Vec[T]] {
    val tpe: Type = vec1.tpe
  }

  /** if (c) x else y. Used to reduce program size  */
  case class Mux[T <: Type](cond: Signal[Bit], vec1: Signal[T], vec2: Signal[T]) extends Signal[T] {
    val tpe: Type = vec1.tpe
  }

  /** x << y and x >> y. Used to reduce program size  */
  case class Shift[S <: Num, T <: Num](vec: Signal[Vec[S]], amount: Signal[Vec[T]], isLeft: Boolean) extends Signal[Vec[S]] {
    val tpe: Type = vec.tpe
  }

  // ---------------- type operations --------------------

  inline def typeOf[T <: Type]: T = inline erasedValue[T] match {
    case Bit           =>
      Bit.asInstanceOf

    case _: ~[t1, t2]  =>
      (new Pair(typeOf[t1], typeOf[t2])).asInstanceOf

    case _: Vec[n]     =>
      val size = valueOf[n]
      Vec(size).asInstanceOf
  }

  def typeOf[T <: Type](value: Value[T]): T = value match {
    case _: BitV      => Bit
    case PairV(l, r)  => new ~(typeOf(l), typeOf(r))
    case VecV(_, s)   => Vec(s).asInstanceOf[T]
  }

  // ---------------- constructors --------------------

  def let[S <: Type, T <: Type](name: String, t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] = {
    val sym = Symbol.fresh(name)
    Let(sym, t, fn(Var(sym, t.tpe)))
  }

  def [S <: Type, T <: Type](t: Signal[S ~ T]) left: Signal[S] = Left(t)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) right: Signal[T] = Right(t)

  object ~ {
    def unapply[S <: Type, T <: Type](sig: Signal[S ~ T]): (Signal[S], Signal[T]) =
      (sig.left, sig.right)

    def unapply[S <: Type, T <: Type](value: Value[S ~ T]): (Value[S], Value[T]) = value match {
      case PairV(lhs, rhs) => (lhs, rhs)
    }
  }

  def fsm[S <: Type, T <: Type](name: String, init: Value[S])(next: Signal[S] => Signal[S ~ T]): Signal[T] = {
    val sym = Symbol.fresh(name)
    Fsm(sym, init, next(Var(sym, typeOf(init))))
  }

  def mux[T <: Type](cond: Signal[Bit], x: Signal[T], y: Signal[T]): Signal[T] = Mux(cond, x, y)

  def [T <: Type](sig: Signal[T]) unary_! : Signal[T] = Not(sig)

  def [T <: Type](lhs: Signal[T]) & (rhs: Signal[T]): Signal[T] = And(lhs, rhs)

  def [T <: Type](lhs: Signal[T]) | (rhs: Signal[T]): Signal[T] = Or(lhs, rhs)

  def [T <: Type](lhs: Signal[T]) ^ (rhs: Signal[T]): Signal[T] = Or(And(lhs, !rhs), And(!lhs, rhs))

  def [T <: Type](value: Value[T]) toSignal: Signal[T] = value match {
    case BitV(b)       => BitLit(b).asInstanceOf
    case PairV(l, r)   => (l.toSignal ~ r.toSignal).asInstanceOf
    case VecV(map, s)  =>
      val bits: List[0 | 1] = (0 until s).map[0 | 1](i => map(i)).toList
      VecLit(bits).asInstanceOf
  }

  inline def variable[T <: Type](name: String): Var[T] =
    Var(Symbol(name), typeOf[T])

  def [S <: Type, T <: Type](lhs: Value[S]) ~ (rhs: Value[T]): Value[S ~ T] =
    new PairV(lhs, rhs)

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Signal[Bit]] = b => BitLit(if b then 1 else 0)
  implicit val lit1: Conversion[1, Signal[Bit]] = one => BitLit(1)
  implicit val lit0: Conversion[0, Signal[Bit]] = zero => BitLit(0)

  /** Int -> Bits */
  def (n: Int) toValue(N: Int): Value[Vec[N.type]] = {
    assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
    assert(n >= 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

    VecV(i => if (n & (1 << i)) == 0 then 0 else 1, N)
  }

  /** Int -> Bits, take the least significant N bits */
  def (n: Int) toSignal(N: Int): Signal[Vec[N.type]] = {
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

  def [N <: Num](vec1: Signal[Vec[N]]) + (vec2: Signal[Vec[N]]): Signal[Vec[N]] =
    Plus(vec1, vec2)

  def [N <: Num](vec1: Signal[Vec[N]]) - (vec2: Signal[Vec[N]]): Signal[Vec[N]] =
    Minus(vec1, vec2)

  val vecEmpty: Signal[Vec[0]] = VecLit[0](Nil)

  def vec[T <: Num](bits: (1 | 0)*): Signal[Vec[T]] =
    VecLit[T](bits.toList)

  def [N <: Num, U <: Num](sig: Signal[Bit]) :: (vec: Signal[Vec[N]]): Signal[Vec[U]] = Cons[N, U](sig, vec)

  def [M <: Num, N <: Num, U <: Num](sig1: Signal[Vec[M]]) ++ (sig2: Signal[Vec[N]]): Signal[Vec[U]] = Concat(sig1, sig2)

  def [S <: Num](vec: Signal[Vec[S]]) apply(index: Int): Signal[Bit] = At(vec, index)

  def [S <: Num, U <: Num](vec: Signal[Vec[S]]) apply(from: Int, to: Int): Signal[Vec[U]] = Range[S, U](vec, from, to)

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
        val padding = 0.toSignal(bitsToShift)
        val shifted: Signal[Vec[N]] =
          if (isLeft) (toShift(bitsToShift, n - 1) ++ padding).as[Vec[N]]
          else (padding ++ toShift(0, n - bitsToShift - 1)).as[Vec[N]]

        val test =
          when (amount(index).as[Bit]) {
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
        val a: Signal[Bit] = vec1(index).as[Bit]
        val b: Signal[Bit] = vec2(index).as[Bit]
        val s: Signal[Bit] = a ^ b ^ cin
        val cout: Signal[Bit] = (a & b ) | (cin & (a ^ b))
        recur(index + 1, cout, (s :: acc.as[Vec[N]]).asInstanceOf)
      }

    recur(0, lit(false), vecEmpty.as[Vec[_]])._2
  }

  /** unsigned subtraction */
  def minus[N <: Num](vec1: Signal[Vec[N]], vec2: Signal[Vec[N]]): Signal[Vec[N]] = {
    val n: Int = vec1.size

    // index starts from least significant bit
    def recur(index: Int, bin: Signal[Bit], acc: Signal[Vec[_]]): (Signal[Bit], Signal[Vec[N]]) =
      if (index >= n) (bin, acc.as[Vec[N]])
      else {
        val a: Signal[Bit] = vec1(index).as[Bit]
        val b: Signal[Bit] = vec2(index).as[Bit]
        val d: Signal[Bit] = a ^ b ^ bin
        val bout: Signal[Bit] = (!a & b) | (!a & bin) | (b & bin)
        recur(index + 1, bout, (d :: acc.as[Vec[N]]).as[Vec[_]])
      }

    recur(0, lit(false), vecEmpty.as[Vec[_]])._2
  }

  /** Concat two bit vectors */
  def concat[M <: Num, N <: Num, U <: Num](sig1: Signal[Vec[M]], sig2: Signal[Vec[N]]): Signal[Vec[U]] = {
    def recur(from: Int, to: Int): Signal[Vec[N]] =
      if (from == to) sig1(from) :: sig2
      else sig1(to) :: recur(from, to - 1)

    if (sig1.size == 0) sig2.as[Vec[U]]
    else if (sig1.size == 1) sig1(0) :: sig2
    else sig1(sig1.size - 1) :: (recur(0, sig1.size - 2))
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

    case _ =>
      equalsBit(x.as[Bit], y.as[Bit])
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

      (0 until n).foldLeft(vecEmpty) { (acc, i) =>
        test1(cond, x.as[Vec[n.type]](i), y.as[Vec[n.type]](i)) :: acc
      }.as[T]

    case _ =>
      test1(cond, x.as[Bit], y.as[Bit]).as[T]
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

        case Range(vec, from, to) =>
          recur(vec) + "(" + from + ", " + to + ")"

        case VecLit(bits)   =>
          toHex(bits)

        case Cons(bit, vec) =>
          recur(bit) + " :: " + recur(vec)

        case Concat(vec1, vec2) =>
          recur(vec1) + " ++ " + recur(vec2)

        case BitLit(value)     =>
          value.toString

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
    case Bit          => "Bit"
    case Pair(t1, t2) => show(t1) + " ~ " + show(t2)
    case Vec(size)    => "Vec[" + size + "]"
  }

  def show(value: Value[_]): String = value match {
    case BitV(value)     => value.toString
    case PairV(l, r)     => show(l) + " ~ " + show(r)
    case VecV(map, size) =>
      toHex((0 until size).map[0 | 1](i => map(i)).toList)
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

        if(sum < 10) sb.append(sum.toString)
        else if(sum == 10) sb.append("A")
        else if(sum == 11) sb.append("B")
        else if(sum == 12) sb.append("C")
        else if(sum == 13) sb.append("D")
        else if(sum == 14) sb.append("E")
        else if(sum == 15) sb.append("F")

        sum = 0
      }

      sb
    }

    sb.toString
  }
}
