package zeno

import examples.Controller

object Main {
  def main(args: Array[String]): Unit = {
    println(Controller.test(args(0)))
  }
}
