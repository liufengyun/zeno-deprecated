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

  sealed trait Type
  object Bit extends Type
  case class Pair[S <: Type, T <: Type](lhs: S, rhs: T) extends Type
  case class Vec[T <: Num](size: T) extends Type

  type ~[S <: Type, T <: Type] = Pair[S, T]
  type Bit = Bit.type
  type Num = Int & Singleton

  // ---------------- values of signal --------------------

  sealed trait Value[T <: Type]

  case class BitV(value: 0 | 1) extends Value[Bit]

  case class PairV[S <: Type, T <: Type](lhs: Value[S], rhs: Value[T]) extends Value[S ~ T]

  case class VecV[T <: Num](map: Int => 0 | 1, size: Int) extends Value[Vec[T]]

  // ---------------- abstract syntax trees --------------------

  // symbol for bindings
  case class Symbol(name: String)

  sealed trait Signal[T <: Type] {
    def unary_! : Signal[T] = Not(this)
    def & (rhs: Signal[T]): Signal[T] = And(this, rhs)
    def | (rhs: Signal[T]): Signal[T] = Or(this, rhs)
    def ^ (rhs: Signal[T]): Signal[T] = Or(And(this, !rhs), And(!this, rhs))
    def ~[U <: Type](rhs: Signal[U]): Signal[T ~ U] = Par(this, rhs)

    def as[S <: Type]: Signal[S] = {
      // TODO: add dynamic check
      this.asInstanceOf
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
    assert(index < vec.size)

    val tpe: Type = Bit
  }

  case class Range[T <: Num, S <: Num](vec: Signal[Vec[T]], from: Int, to: Int) extends Signal[Vec[S]] {
    assert(from < vec.size && from >= 0)
    assert(to < vec.size && from >= 0)
    assert(from <= to)

    val tpe: Type = {
      val size = to - from + 1
      Vec(size)
    }
  }

  /** Empty vector */
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

  case class Circuit[S <: Type, T <: Type](in: Var[S], body: Signal[T])

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
    case VecV(_, s)   => Vec(s).asInstanceOf
  }

  // ---------------- constructors --------------------

  def let[S <: Type, T <: Type](name: String, t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] = {
    val sym = Symbol(name)
    Let(sym, t, fn(Var(sym, t.tpe)))
  }

  def [S <: Type, T <: Type](t: Signal[S ~ T]) left: Signal[S] = Left(t)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) right: Signal[T] = Right(t)

  object ~ {
    def unapply[S <: Type, T <: Type](sig: Signal[S ~ T]): (Signal[S], Signal[T]) =
      (sig.left, sig.right)
  }

  def fsm[S <: Type, T <: Type](name: String, init: Value[S])(next: Signal[S] => Signal[S ~ T]): Signal[T] = {
    val sym = Symbol(name)
    Fsm(sym, init, next(Var(sym, typeOf(init))))
  }

  val vecEmpty: Signal[Vec[0]] = VecLit[0](Nil)

  def vec[T <: Num](bits: (1 | 0)*): Signal[Vec[T]] =
    VecLit[T](bits.toList)

  def [T <: Type](value: Value[T]) toSignal: Signal[T] = value match {
    case BitV(b)       => BitLit(b).asInstanceOf
    case PairV(l, r)   => (l.toSignal ~ r.toSignal).asInstanceOf
    case VecV(map, s)  =>
      val bits: List[0 | 1] = (0 until s).map[0 | 1](i => map(i)).toList
      VecLit(bits).asInstanceOf
  }

  inline def input[T <: Type](name: String): Signal[T] =
    Var(Symbol(name), typeOf[T])

  def [S <: Type, T <: Type](lhs: Value[S]) ~ (rhs: Value[T]): Value[S ~ T] =
    new PairV(lhs, rhs)

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Signal[Bit]] = b => BitLit(if b then 1 else 0)
  implicit val lit1: Conversion[1, Signal[Bit]] = one => BitLit(1)
  implicit val lit0: Conversion[0, Signal[Bit]] = zero => BitLit(0)

  // ---------------- bit vector operations --------------------

  def [N <: Num](vec: Signal[Vec[N]]) size: Int = vec.tpe.asInstanceOf[Vec[N]].size

  private  def shiftImpl[M <: Num, N <: Num](vec: Signal[Vec[M]], amount: Signal[Vec[N]], isLeft: Boolean): Signal[Vec[M]] = {
    val n: Int = vec.size
    val m: Int = amount.size

    // index starts from least significant bit of `amount`
    def recur(index: Int, toShift: Signal[Vec[M]]): Signal[Vec[M]] =
      if (index >= m) toShift
      else {
        val bitsToShift = 1 << index
        val padding = 0.toSignal(bitsToShift)
        val shifted: Signal[Vec[M]] =
          if (isLeft) (toShift(bitsToShift, n) ++ padding).as[Vec[M]]
          else (padding ++ toShift(0, n - bitsToShift)).as[Vec[M]]

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
  def [M <: Num, N <: Num](vec: Signal[Vec[M]]) << (amount: Signal[Vec[N]]): Signal[Vec[M]] =
    shiftImpl(vec, amount, isLeft = true)

  /** logical shift  right */
  def [M <: Num, N <: Num](vec: Signal[Vec[M]]) >> (amount: Signal[Vec[N]]): Signal[Vec[M]] =
    shiftImpl(vec, amount, isLeft = false)

  /** unsigned addition, ripple-carry adder */
  def [N <: Num](vec1: Signal[Vec[N]]) + (vec2: Signal[Vec[N]]): Signal[Vec[N]] = {
    val n: Int = vec1.size

    // index starts from least significant bit
    def recur(index: Int, cin: Signal[Bit], acc: Signal[Vec[_]]): (Signal[Bit], Signal[Vec[N]]) =
      if (index >= n) (cin, acc.asInstanceOf)
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
  def [N <: Num](vec1: Signal[Vec[N]]) - (vec2: Signal[Vec[N]]): Signal[Vec[N]] = {
    val n: Int = vec1.size

    // index starts from least significant bit
    def recur(index: Int, bin: Signal[Bit], acc: Signal[Vec[_]]): (Signal[Bit], Signal[Vec[N]]) =
      if (index >= n) (bin, acc.asInstanceOf)
      else {
        val a: Signal[Bit] = vec1(index).as[Bit]
        val b: Signal[Bit] = vec2(index).as[Bit]
        val d: Signal[Bit] = a ^ b ^ bin
        val bout: Signal[Bit] = (!a & b) | (!a & bin) | (b & bin)
        recur(index + 1, bout, (d :: acc.as[Vec[N]]).asInstanceOf)
      }

    recur(0, lit(false), vecEmpty.as[Vec[_]])._2
  }

  /** Int -> Bits */
  def (n: Int) toValue(N: Int): Value[Vec[N.type]] = {
    assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
    assert(n > 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

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

  def [N <: Num, U <: Num](sig: Signal[Bit]) :: (vec: Signal[Vec[N]]): Signal[Vec[U]] = Cons[N, U](sig, vec)

  /** Concat two bit vectors */
  def [M <: Num, N <: Num, U <: Num](sig1: Signal[Vec[M]]) ++ (sig2: Signal[Vec[N]]): Signal[Vec[U]] =
    if (sig1.size == 0) sig2.asInstanceOf
    else sig1(0) :: (sig1(1, sig1.size - 1) ++ sig2)

  def [S <: Num](vec: Signal[Vec[S]]) apply(index: Int): Signal[Bit] = At(vec, index)

  def [S <: Num, U <: Num](vec: Signal[Vec[S]]) apply(from: Int, to: Int): Signal[Vec[U]] = Range[S, U](vec, from, to)

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
      (test(cond, x1.left, y1.left) ~ test(cond, x1.right, y1.right)).asInstanceOf

    case Vec(n) =>
      (0 until n).foldLeft(vecEmpty) { (acc, i) =>
        test1(cond, x.as[Vec[n.type]](i), y.as[Vec[n.type]](i)) :: acc
      }.asInstanceOf

    case _ =>
      test1(cond, x.as[Bit], y.as[Bit]).asInstanceOf
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
     WhenCont(r => test(cond, x, r))
  class WhenCont[T <: Type](cont: Signal[T] => Signal[T]) {
    def otherwise(y: Signal[T]): Signal[T] = cont(y)
    def when (cond2: Signal[Bit])(z: Signal[T]): WhenCont[T] =
      WhenCont(r => cont(test(cond2, z, r)))
  }

  def equalBit(x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (x & y) | (!x & !y)
  def [T <: Type](x: Signal[T]) === (y: Signal[T]): Signal[Bit] =  x.tpe match {
    case Pair(t1, t2) =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.asInstanceOf[Signal[T1 ~ T2]]
      val y1 = y.asInstanceOf[Signal[T1 ~ T2]]
      (x1.left === y1.left) & (x1.right === y1.right)

    case Vec(n) =>
      (0 until n).map { i =>
        equalBit(x.as[Vec[n.type]](i), y.as[Vec[n.type]](i))
      }.reduce(_ & _)


    case _ =>
      equalBit(x.asInstanceOf[Signal[Bit]], y.asInstanceOf[Signal[Bit]])
  }

  // ---------------- pretty print --------------------


  // TODO
  // 1. adder
  // 2. multiplier
  // 3. average filter
  // 4. 2nd order filter : synchronous paper
  // 5. Lucid synchronous
}