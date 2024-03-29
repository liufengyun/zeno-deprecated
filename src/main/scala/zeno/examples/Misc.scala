package zeno
package examples

import lang._

object Misc {
  def test1(cond: Sig[Bit], x: Sig[Bit], y: Sig[Bit]): Sig[Bit] = (!cond | x) & (cond | y)
  def test[T <: Type](cond: Sig[Bit], x: Sig[T], y: Sig[T]): Sig[T] = x.tpe match {
    case t1 ~ t2 =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.as[T1 ~ T2]
      val y1 = y.as[T1 ~ T2]
      (mux(cond, x1.left, y1.left) ~ mux(cond, x1.right, y1.right)).as[T]

    case Vec(n) =>
      val xSize = x.as[Vec[0]].width
      val ySize = y.as[Vec[0]].width
      assert(xSize == ySize, "x.width = " +  xSize + ", y.width = " +  ySize)

      (0 until n).foldLeft(Vec()) { (acc, i) =>
        test1(cond, x.as[Vec[n.type]](i), y.as[Vec[n.type]](i)) ++ acc
      }.as[T]

    case _ => ??? // impossible
  }

  private  def shiftImpl[M <: Num, N <: Num](vec: Sig[Vec[N]], amount: Sig[Vec[M]], isLeft: Boolean): Sig[Vec[N]] = {
    val n: Int = vec.width
    val m: Int = amount.width

    // index starts from least significant bit of `amount`
    def recur(index: Int, toShift: Sig[Vec[N]]): Sig[Vec[N]] =
      if (index >= m) toShift
      else {
        val bitsToShift = 1 << index
        val padding = 0.toSig(bitsToShift)
        val shifted: Sig[Vec[N]] =
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
  def shiftLeft[M <: Num, N <: Num](vec: Sig[Vec[M]], amount: Sig[Vec[N]]): Sig[Vec[M]] =
    shiftImpl(vec, amount, isLeft = true)

  /** logical shift  right */
  def shiftRight[M <: Num, N <: Num](vec: Sig[Vec[M]], amount: Sig[Vec[N]]): Sig[Vec[M]] =
    shiftImpl(vec, amount, isLeft = false)

  /** unsigned addition, ripple-carry adder */
  def plus[N <: Num](vec1: Sig[Vec[N]], vec2: Sig[Vec[N]]): Sig[Vec[N]] = {
    val n: Int = vec1.width

    // index starts from least significant bit
    def recur(index: Int, cin: Sig[Bit], acc: Sig[Vec[_]]): (Sig[Bit], Sig[Vec[N]]) =
      if (index >= n) (cin, acc.as[Vec[N]])
      else {
        val a: Sig[Bit] = vec1(index)
        val b: Sig[Bit] = vec2(index)
        val s: Sig[Bit] = a ^ b ^ cin
        val cout: Sig[Bit] = (a & b ) | (cin & (a ^ b))
        recur(index + 1, cout, (s ++ acc.as[Vec[N]]).asInstanceOf)
      }

    recur(0, lit(false), Vec().as[Vec[_]])._2
  }

  /** unsigned subtraction */
  def minus[N <: Num](vec1: Sig[Vec[N]], vec2: Sig[Vec[N]]): Sig[Vec[N]] = {
    val n: Int = vec1.width

    // index starts from least significant bit
    def recur(index: Int, bin: Sig[Bit], acc: Sig[Vec[_]]): (Sig[Bit], Sig[Vec[N]]) =
      if (index >= n) (bin, acc.as[Vec[N]])
      else {
        val a: Sig[Bit] = vec1(index)
        val b: Sig[Bit] = vec2(index)
        val d: Sig[Bit] = a ^ b ^ bin
        val bout: Sig[Bit] = (!a & b) | (!a & bin) | (b & bin)
        recur(index + 1, bout, (d ++ acc.as[Vec[N]]).as[Vec[_]])
      }

    recur(0, lit(false), Vec().as[Vec[_]])._2
  }

  /** Concat two bit vectors */
  def concat[M <: Num, N <: Num, U <: Num](sig1: Sig[Vec[M]], sig2: Sig[Vec[N]]): Sig[Vec[U]] = {
    def recur(index: Int): Sig[Vec[N]] =
      if (index == 0) sig1(0) ++ sig2
      else sig1(index) ++ recur(index - 1)

    if (sig1.width == 0) sig2.as[Vec[U]]
    else recur(sig1.width - 1).as[Vec[U]]
  }

  def equalsBit(x: Sig[Bit], y: Sig[Bit]): Sig[Bit] = (x & y) | (!x & !y)
  def equals[T <: Type](x: Sig[T], y: Sig[T]): Sig[Bit] =  x.tpe match {
    case t1 ~ t2 =>
      type T1 <: Type
      type T2 <: Type
      val x1 = x.as[T1 ~ T2]
      val y1 = y.as[T1 ~ T2]
      equals(x1.left, y1.left) & equals(x1.right, y1.right)

    case Vec(n) =>
      (0 until n).map { i =>
        equalsBit(x.as[Vec[n.type]](i), y.as[Vec[n.type]](i))
      }.reduce(_ & _)

    case _ => ??? // impossible
  }
}