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

  // values of signal
  sealed trait Data
  case class Bit(value: Boolean) extends Data
  case class ~[S <: Data, T <: Data](lhs: S, rhs: T) extends Data

  case class Symbol(name: String)

  sealed trait Signal[T <: Data] {
    def unary_! : Signal[T] = Not(this)
    def && (rhs: Signal[T]): Signal[T] = And(this, rhs)
    def || (rhs: Signal[T]): Signal[T] = Or(this, rhs)
    def ^ (rhs: Signal[T]): Signal[T] = Or(And(this, !rhs), And(!this, rhs))
    def ~[U <: Data](rhs: Signal[U]): Signal[T ~ U] = Pair(this, rhs)

    def as[S <: Data]: Signal[S] = {
      // TODO: add dynamic check
      this.asInstanceOf
    }

    def schema: Data
  }

  case class Pair[S <: Data, T <: Data](lhs: Signal[S], rhs: Signal[T]) extends Signal[S ~ T] {
    val schema: Data = new ~(lhs.schema, rhs.schema)
  }

  case class Left[S <: Data, T <: Data](pair: Signal[S ~ T]) extends Signal[S] {
    val schema: Data = pair.schema match {
      case s1 ~ s2 => s1
      case _ => ???  // impossible
    }
  }

  case class Right[S <: Data, T <: Data](pair: Signal[S ~ T]) extends Signal[T] {
    val schema: Data = pair.schema match {
      case s1 ~ s2 => s2
      case _ => ???  // impossible
    }
  }

  case class Var[T <: Data](sym: Symbol, schema: Data) extends Signal[T]

  case class Let[S <: Data, T <: Data](sym: Symbol, sig: Signal[S],  body: Signal[T]) extends Signal[T] {
    val schema: Data = body.schema
  }

  case class Fsm[S <: Data, T <: Data](sym: Symbol, init: S, body: Signal[S ~ T]) extends Signal[T] {
    val schema: Data = body.schema match {
      case s1 ~ s2 => s2
      case _ => ???  // impossible
    }
  }

  case class Lit(value: Bit) extends Signal[Bit] {
    val schema: Data = Bit(true)
  }

  case class And[T <: Data](lhs: Signal[T], rhs: Signal[T]) extends Signal[T] {
    assert(lhs.schema == rhs.schema)
    val schema: Data = lhs.schema
  }

  case class Or[T <: Data](lhs: Signal[T], rhs: Signal[T]) extends Signal[T] {
    assert(lhs.schema == rhs.schema)
    val schema: Data = lhs.schema
  }

  case class Not[T <: Data](in: Signal[T]) extends Signal[T] {
    val schema: Data = in.schema
  }

  case class Circuit[S <: Data, T <: Data](in: Var[S], body: Signal[T])

  // ---------------- constructors --------------------

  def let[S <: Data, T <: Data](name: String, t: Signal[S])(fn: Signal[S] => Signal[T]): Signal[T] = {
    val sym = Symbol(name)
    Let(sym, t, fn(Var(sym, t.schema)))
  }

  def [S <: Data, T <: Data](t: Signal[S ~ T]) _1: Signal[S] = Left(t)

  def [S <: Data, T <: Data](t: Signal[S ~ T]) _2: Signal[T] = Right(t)

  def fsm[S <: Data, T <: Data](name: String, init: S)(next: Signal[S] => Signal[S ~ T]): Signal[T] = {
    val sym = Symbol(name)
    Fsm(sym, init, next(Var(sym, init)))
  }

  def [T <: Data](data: T) toSignal: Signal[T] = data match {
    case b: Bit => Lit(b).asInstanceOf
    case l ~ r  => (l.toSignal ~ r.toSignal).asInstanceOf
  }

  inline def input[T <: Data](name: String): Signal[T] =
    Var(Symbol(name), schemaOf[T])

  inline def schemaOf[T <: Data]: T = inline erasedValue[T] match {
    case _: Bit        => true.asInstanceOf
    case _: ~[t1, t2]  => (new ~(schemaOf[t1], schemaOf[t2])).asInstanceOf
  }

  def [S <: Data, T <: Data](lhs: S) ~ (rhs: T): S ~ T = new ~(lhs, rhs)

  // Boolean -> Bits
  implicit val lit: Conversion[Boolean, Signal[Bit]] = b => Lit(Bit(b))

  // ---------------- bit vector operations --------------------
  type Num = Int & Singleton

  type Vec[N <: Num] <: Data = N match {
    case 1 => Bit
    case S[n] => Bit ~ Vec[n]
  }

  def [N <: Num](vec: Signal[Vec[N]]) size: N = {
    def recur(schema: Data): Int = schema match {
      case _: Bit => 1
      case (_: Bit) ~ s =>  1 + recur(s)
    }
    recur(vec.schema).asInstanceOf
  }

  // logical shift left
  def [N <: Num, M <: Num](vec: Signal[Vec[N]]) << (amount: Signal[Vec[M]]): Signal[Vec[N]] = {
    val n: N = vec.size
    val m: M = amount.size

    // index starts from lowest bit of `amount`
    def recur(index: Int, toShift: Signal[Data]): Signal[Data] =
      if (index > m) toShift
      else {
        val bitsToShift = 1 << index
        val padding = 0.toSignal(bitsToShift).as[Data]
        val shifted: Signal[Data] =
          when (amount.at(index).as[Bit]) {
            (toShift.range(bitsToShift, n) ~ padding).as[Data]
          } otherwise {
            toShift
          }
        recur(index + 1, shifted)
      }

    recur(0, vec.as[Data]).asInstanceOf
  }

  // logical shift  right
  def [N <: Num, M <: Num](vec: Signal[Vec[N]]) >> (amount: Signal[Vec[M]]): Signal[Vec[N]] = {
    val n: N = vec.size
    val m: M = amount.size

    // index starts from lowest bit of `amount`
    def recur(index: Int, toShift: Signal[Data]): Signal[Data] =
      if (index > m) toShift
      else {
        val bitsToShift = 1 << index
        val padding = 0.toSignal(bitsToShift).as[Data]
        val shifted: Signal[Data] =
          when  (amount.at(index).as[Bit]) {
            (padding ~ toShift.range(0, n - bitsToShift)).as[Data]
          } otherwise {
            toShift
          }
        recur(index + 1, shifted)
      }

    recur(0, vec.as[Data]).asInstanceOf
  }


  // add

  // sub

  // Int -> Bits
  def (n: Int) toVec(N: Int): Vec[N.type] = {
    assert(N > 0 && N <= 32, "N = " + N + ", expect N > 0 && N <= 32")
    assert(n > 0, "n = " + n + ", expect n > 0") // TODO: no negative numbers for now

    var res: Data = null
    var shift = 1 << N
    while (shift > 0) {
      val b = (n & (1 << shift)) == 0
      res = if (res == null) Bit(b) else new ~(res, Bit(b))
      shift = shift >> 1
    }

    res.asInstanceOf
  }

  // Int -> Bits
  def (n: Int) toSignal(N: Int): Signal[Vec[N.type]] =
    n.toVec(N).toSignal[Vec[N.type]]

  // ---------------- range operations --------------------

  def [S <: Data](sig: Signal[S]) at(index: Int): Signal[_] = {
    assert(index >= 0)
    if (index == 0) sig.asInstanceOf
    else sig.schema match {
      case b: Bit  => throw new Exception("index out of range")
      case s1 ~ s2 => sig.as[Data ~ Data]._2.at(index - 1)
    }
  }

  def [S <: Data](sig: Signal[S]) range(from: Int, to: Int): Signal[_] = {
    assert(from >= 0 && to >=0 && from < to)
    def recur[T <: Data](sig: Signal[T], acc: Signal[_], curIndex: Int): Signal[_] = {
      if (curIndex == to) acc
      else sig.schema match {
        case b: Bit  => throw new Exception("index out of range")
        case s1 ~ s2 =>
          val sig2 = sig.as[Data ~ Data]
          if (curIndex < from) recur(sig2._2, acc, curIndex + 1)
          else recur(sig2._2, if (acc == null) sig2._1 else acc ~ sig2._1, curIndex + 1)
      }
    }
    recur(sig, null, 0)
  }

  // ----------------  utilities --------------------

  // Tuple -> Pair
  implicit def tuple2toPair[S <: Data, T <: Data]: Conversion[(Signal[S], Signal[T]), Signal[S ~ T]] =
    t2 => t2._1 ~ t2._2

  implicit def tuple3toPair[T1 <: Data, T2 <: Data, T3 <: Data]: Conversion[(Signal[T1], Signal[T2], Signal[T3]), Signal[T1 ~ T2 ~ T3]] =
    t3 => t3._1 ~ t3._2 ~ t3._3

  def test1(cond: Signal[Bit], x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (!cond || x) && (cond || y)
  def test[T <: Data](cond: Signal[Bit], x: Signal[T], y: Signal[T]): Signal[T] = x.schema match {
    case s1 ~ s2 =>
      type T1 <: Data
      type T2 <: Data
      val x1 = x.asInstanceOf[Signal[T1 ~ T2]]
      val y1 = y.asInstanceOf[Signal[T1 ~ T2]]
      (test(cond, x1._1, y1._1) ~ test(cond, x1._2, y1._2)).asInstanceOf
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
  def when[T <: Data](cond: Signal[Bit])(x: => Signal[T]): WhenCont[T] =
     WhenCont(r => test(cond, x, r))
  class WhenCont[T <: Data](cont: Signal[T] => Signal[T]) {
    def otherwise(y: Signal[T]): Signal[T] = cont(y)
    def when (cond2: Signal[Bit])(z: Signal[T]): WhenCont[T] =
      WhenCont(r => cont(test(cond2, z, r)))
  }

  def equalBit(x: Signal[Bit], y: Signal[Bit]): Signal[Bit] = (x && y) || (!x && !y)
  def [T <: Data](x: Signal[T]) === (y: Signal[T]): Signal[Bit] =  x.schema match {
    case s1 ~ s2 =>
      type T1 <: Data
      type T2 <: Data
      val x1 = x.asInstanceOf[Signal[T1 ~ T2]]
      val y1 = y.asInstanceOf[Signal[T1 ~ T2]]
      ??? // x1._1 === y1._1 && x1._2 === y1._2
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