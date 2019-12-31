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
  case class ~[S <: Type, T <: Type](lhs: S, rhs: T) extends Type

  type Bit = Bit.type

  // ---------------- values of signal --------------------

  sealed trait Value[T <: Type]

  case class BitV(value: Boolean) extends Value[Bit]

  case class PairV[S <: Type, T <: Type](lhs: Value[S], rhs: Value[T]) extends Value[S ~ T]

  // ---------------- abstract syntax trees --------------------

  // symbol for bindings
  case class Symbol(name: String)

  sealed trait Signal[T <: Type] {
    def unary_! : Signal[T] = Not(this)
    def && (rhs: Signal[T]): Signal[T] = And(this, rhs)
    def || (rhs: Signal[T]): Signal[T] = Or(this, rhs)
    def ^ (rhs: Signal[T]): Signal[T] = Or(And(this, !rhs), And(!this, rhs))
    def ~[U <: Type](rhs: Signal[U]): Signal[T ~ U] = Pair(this, rhs)

    def as[S <: Type]: Signal[S] = {
      // TODO: add dynamic check
      this.asInstanceOf
    }

    def tpe: Type
  }

  case class Pair[S <: Type, T <: Type](lhs: Signal[S], rhs: Signal[T]) extends Signal[S ~ T] {
    val tpe: Type = new ~(lhs.tpe, rhs.tpe)
  }

  case class Left[S <: Type, T <: Type](pair: Signal[S ~ T]) extends Signal[S] {
    val tpe: Type = pair.tpe match {
      case s1 ~ s2 => s1
      case _ => ???  // impossible
    }
  }

  case class Right[S <: Type, T <: Type](pair: Signal[S ~ T]) extends Signal[T] {
    val tpe: Type = pair.tpe match {
      case s1 ~ s2 => s2
      case _ => ???  // impossible
    }
  }

  case class Var[T <: Type](sym: Symbol, tpe: Type) extends Signal[T]

  case class Let[S <: Type, T <: Type](sym: Symbol, sig: Signal[S],  body: Signal[T]) extends Signal[T] {
    val tpe: Type = body.tpe
  }

  case class Fsm[S <: Type, T <: Type](sym: Symbol, init: Value[S], body: Signal[S ~ T]) extends Signal[T] {
    val tpe: Type = body.tpe match {
      case s1 ~ s2 => s2
      case _ => ???  // impossible
    }
  }

  case class Lit(value: Boolean) extends Signal[Bit] {
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
    case Bit           => Bit.asInstanceOf
    case _: ~[t1, t2]  => (new ~(typeOf[t1], typeOf[t2])).asInstanceOf
  }

  def typeOf[T <: Type](value: Value[T]): T = value match {
    case _: BitV      => Bit
    case PairV(l, r)  => new ~(typeOf(l), typeOf(r))
  }
  // ---------------- constructors --------------------

  def let[S <: Type, T <: Type](name: String, t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] = {
    val sym = Symbol(name)
    Let(sym, t, fn(Var(sym, t.tpe)))
  }

  def [S <: Type, T <: Type](t: Signal[S ~ T]) left: Signal[S] = Left(t)

  def [S <: Type, T <: Type](t: Signal[S ~ T]) right: Signal[T] = Right(t)

  def fsm[S <: Type, T <: Type](name: String, init: Value[S])(next: Signal[S] => Signal[S ~ T]): Signal[T] = {
    val sym = Symbol(name)
    Fsm(sym, init, next(Var(sym, typeOf(init))))
  }

  def [T <: Type](value: Value[T]) toSignal: Signal[T] = value match {
    case BitV(b)       => Lit(b).asInstanceOf
    case PairV(l, r)   => (l.toSignal ~ r.toSignal).asInstanceOf
  }

  inline def input[T <: Type](name: String): Signal[T] =
    Var(Symbol(name), typeOf[T])

  def [S <: Type, T <: Type](lhs: Value[S]) ~ (rhs: Value[T]): Value[S ~ T] =
    new PairV(lhs, rhs)

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Signal[Bit]] = b => Lit(b)

  // ---------------- bit vector operations --------------------
  type Num = Int & Singleton

  type Vec[N <: Num] <: Type = N match {
    case 1 => Bit
    case S[n] => Bit ~ Vec[n]
  }

  def [N <: Num](vec: Signal[Vec[N]]) size: N = {
    def recur(tpe: Type): Int = tpe match {
      case _: Bit => 1
      case (_: Bit) ~ s =>  1 + recur(s)
    }
    recur(vec.tpe).asInstanceOf
  }

  private  def shiftImpl[N <: Num, M <: Num](vec: Signal[Vec[N]], amount: Signal[Vec[M]], isLeft: Boolean): Signal[Vec[N]] = {
    val n: N = vec.size
    val m: M = amount.size

    // index starts from least significant bit of `amount`
    def recur(index: Int, toShift: Signal[Type]): Signal[Type] =
      if (index >= m) toShift
      else {
        val bitsToShift = 1 << index
        val padding = 0.toSignal(bitsToShift).as[Type]
        val shifted =
          if (isLeft) (toShift.range(bitsToShift, n) ~ padding).as[Type]
          else (padding ~ toShift.range(0, n - bitsToShift)).as[Type]

        val test: Signal[Type] =
          when (amount.at(index).as[Bit]) {
            shifted
          } otherwise {
            toShift
          }
        recur(index + 1, test)
      }

    recur(0, vec.as[Type]).asInstanceOf
  }


  // logical shift left
  def [N <: Num, M <: Num](vec: Signal[Vec[N]]) << (amount: Signal[Vec[M]]): Signal[Vec[N]] =
    shiftImpl(vec, amount, isLeft = true)

  // logical shift  right
  def [N <: Num, M <: Num](vec: Signal[Vec[N]]) >> (amount: Signal[Vec[M]]): Signal[Vec[N]] =
    shiftImpl(vec, amount, isLeft = false)

  // unsigned addition, ripple-carry adder
  def [N <: Num](vec1: Signal[Vec[N]]) + (vec2: Signal[Vec[N]]): (Signal[Bit], Signal[Vec[N]]) = {
    val n: N = vec1.size

    // index starts from least significant bit
    def recur(index: Int, cin: Signal[Bit], acc: Signal[_]): (Signal[Bit], Signal[_]) =
      if (index >= n) (cin, acc)
      else {
        val a: Signal[Bit] = vec1.at(index).as[Bit]
        val b: Signal[Bit] = vec2.at(index).as[Bit]
        val s: Signal[Bit] = a ^ b ^ cin
        val cout: Signal[Bit] = (a && b ) || (cin && (a ^ b))
        recur(index + 1, cout, if (acc == null) s else s ~ acc)
      }

    recur(0, lit(false), null).asInstanceOf
  }

  // unsigned subtraction
  def [N <: Num](vec1: Signal[Vec[N]]) - (vec2: Signal[Vec[N]]): (Signal[Bit], Signal[Vec[N]]) = {
    val n: N = vec1.size

    // index starts from least significant bit
    def recur(index: Int, bin: Signal[Bit], acc: Signal[_]): (Signal[Bit], Signal[_]) =
      if (index >= n) (bin, acc)
      else {
        val a: Signal[Bit] = vec1.at(index).as[Bit]
        val b: Signal[Bit] = vec2.at(index).as[Bit]
        val d: Signal[Bit] = a ^ b ^ bin
        val bout: Signal[Bit] = (!a && b) || (!a && bin) || (b && bin)
        recur(index + 1, bout, if (acc == null) d else d ~ acc)
      }

    recur(0, lit(false), null).asInstanceOf
  }

  // Int -> Bits
  def (n: Int) toValue(N: Int): Value[Vec[N.type]] = {
    assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
    assert(n > 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

    var res: Value[_] = null
    var shift = 1 << N
    while (shift > 0) {
      val b = (n & (1 << shift)) == 0
      res = if (res == null) BitV(b) else new PairV(res, BitV(b))
      shift = shift >> 1
    }

    res.asInstanceOf
  }

  // Int -> Bits
  def (n: Int) toSignal(N: Int): Signal[Vec[N.type]] =
    n.toValue(N).toSignal[Vec[N.type]]

  // ---------------- range operations --------------------

  def [S <: Type](sig: Signal[S]) at(index: Int): Signal[_] = {
    assert(index >= 0)
    if (index == 0) sig.asInstanceOf
    else sig.tpe match {
      case Bit     => throw new Exception("index out of range")
      case s1 ~ s2 => sig.as[Type ~ Type].right.at(index - 1)
    }
  }

  def [S <: Type](sig: Signal[S]) range(from: Int, to: Int): Signal[_] = {
    assert(from >= 0 && to >=0 && from < to)
    def recur[T <: Type](sig: Signal[T], acc: Signal[_], curIndex: Int): Signal[_] = {
      if (curIndex == to) acc
      else sig.tpe match {
        case b: Bit  => throw new Exception("index out of range")
        case s1 ~ s2 =>
          val sig2 = sig.as[Type ~ Type]
          if (curIndex < from) recur(sig2.right, acc, curIndex + 1)
          else recur(sig2.right, if (acc == null) sig2.left else acc ~ sig2.left, curIndex + 1)
      }
    }
    recur(sig, null, 0)
  }

  // ----------------  utilities --------------------

  // Tuple -> Pair
  implicit def tuple2toPair[S <: Type, T <: Type]: Conversion[(Signal[S], Signal[T]), Signal[S ~ T]] =
    t2 => t2._1 ~ t2._2

  implicit def tuple3toPair[T1 <: Type, T2 <: Type, T3 <: Type]: Conversion[(Signal[T1], Signal[T2], Signal[T3]), Signal[T1 ~ T2 ~ T3]] =
    t3 => t3._1 ~ t3._2 ~ t3._3

  def test1(cond: Signal[Bit], x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (!cond || x) && (cond || y)
  def test[T <: Type](cond: Signal[Bit], x: Signal[T], y: Signal[T]): Signal[T] = x.tpe match {
    case s1 ~ s2 =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.asInstanceOf[Signal[T1 ~ T2]]
      val y1 = y.asInstanceOf[Signal[T1 ~ T2]]
      (test(cond, x1.left, y1.left) ~ test(cond, x1.right, y1.right)).asInstanceOf
    case _ =>
      test1(cond, x.asInstanceOf[Signal[Bit]], y.asInstanceOf[Signal[Bit]]).asInstanceOf
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
  def when[T <: Type](cond: Signal[Bit])(x: => Signal[T]): WhenCont[T] =
     WhenCont(r => test(cond, x, r))
  class WhenCont[T <: Type](cont: Signal[T] => Signal[T]) {
    def otherwise(y: Signal[T]): Signal[T] = cont(y)
    def when (cond2: Signal[Bit])(z: Signal[T]): WhenCont[T] =
      WhenCont(r => cont(test(cond2, z, r)))
  }

  def equalBit(x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (x && y) || (!x && !y)
  def [T <: Type](x: Signal[T]) === (y: Signal[T]): Signal[Bit] =  x.tpe match {
    case s1 ~ s2 =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.asInstanceOf[Signal[T1 ~ T2]]
      val y1 = y.asInstanceOf[Signal[T1 ~ T2]]
      (x1.left === y1.left) && (x1.right === y1.right)
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