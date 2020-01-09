package nand
package util

import lang._

object Tracing {
  val enable = false
  var depth: Int = 0
  val indentTab = " "

  def trace[T](msg: => String, show: T => String)(op: => T): T = if (enable) {
    traceIndented(s"==> ${msg}?")
    // displayPrompt()
    depth += 1
    val res = op
    depth -= 1
    traceIndented(s"<== ${msg} = ${show(res)}")
    res
  } else op

  def trace[T <: Type](msg: => String)(op: => Signal[T]): Signal[T] =
    trace(msg, (x: Signal[T]) => x.show)(op)

  def traceOp(msg: => String)(op: => Unit): Unit = {
    traceIndented(s"==> ${msg}")
    depth += 1
    op
    depth -= 1
    traceIndented(s"<== ${msg}")
  }

  def pad(s: String, padFirst: Boolean = false) = {
    val padding = indentTab * depth
    s.split("\n").mkString(if (padFirst) padding else "", "\n" + padding, "")
  }

  def traceIndented(msg: => String) =
    if (enable) println(pad(msg, padFirst = true))

  /** Show prompt if `-Xprompt` is passed as a flag to the compiler */
  def displayPrompt(): Unit = {
    println()
    print("a)bort, s)tack, r)esume: ")
    def loop(): Unit = System.in.read() match {
      case 'a' | 'A' =>
        new Throwable().printStackTrace()
        System.exit(1)
      case 's' | 'S' =>
        new Throwable().printStackTrace()
        println()
      case 'r' | 'R' =>
        ()
      case _ =>
        loop()
    }
    loop()
  }
}