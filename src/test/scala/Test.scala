package ysm

import org.junit.Test
import org.junit.Assert._

import java.nio.charset.StandardCharsets._
import java.nio.file.{Files, Paths, FileSystems, Path}
import java.io.File

import lang._
import phases._

import scala.language.implicitConversions
class TestSuite {
  @Test def controller(): Unit = {
    var  success: Boolean = true

    val path = new java.io.File("asm")
    path.listFiles.filter(f => f.isFile && f.getName.endsWith(".s")).foreach { f =>
      checkResult(Controller.test(f.toString))
      checkResult(Controller.testDetupled(f.toString))

      def checkResult(res: String) = {
        val checkFile = f.toString + ".check"
        val check =
          if (new File(checkFile).exists)
            new String(Files.readAllBytes(Paths.get(checkFile)), UTF_8)
          else
            "<empty>"
        val msg = "expected = " + check + ", found = " + res

        if (check.trim == res) println(Console.GREEN + msg + Console.RESET)
        else println(Console.RED + msg + Console.RESET)

        success = success && check.trim == res
      }
    }

    // run all tests by default
    assertTrue(success)

    // generate verilog

    val busIn = variable[Controller.BusIn]("busIn")
    val instructions = Assembler.assemble("asm/jump.s")
    val code = Controller.processor(instructions, busIn)
    writeFile("verilog/controller.v", toVerilog("Controller", List(busIn), code))
  }

  @Test def adder2(): Unit = {
    val a = variable[Vec[2]]("a")
    val b = variable[Vec[2]]("b")
    val circuit = Adder.adder2(a, b)
    val add2 = interpret(List(a, b), circuit)

    writeFile("verilog/adder.v", toVerilog("Adder", List(a, b), circuit))

    {
      val Value(c1, s1, s0) = add2(Value(1, 0) :: Value(0, 1) :: Nil)
      assertEquals(c1, 0)
      assertEquals(s1, 1)
      assertEquals(s0, 1)
    }

    {
      val Value(c1, s1, s0) = add2(Value(1, 0) :: Value(1, 1) :: Nil)
      assertEquals(c1, 1)
      assertEquals(s1, 0)
      assertEquals(s0, 1)
    }
  }

  @Test def adderN(): Unit = {
    val a = variable[Vec[3]]("a")
    val b = variable[Vec[3]]("b")
    val circuit = Adder.adderN(a, b)
    val add3 = interpret(List(a, b), circuit)

    {
      val Value(c2) ~ Value(s2, s1, s0) = add3(Value(1, 0, 1) :: Value(0, 1, 0) :: Nil)
      assertEquals(c2, 0)
      assertEquals(s2, 1)
      assertEquals(s1, 1)
      assertEquals(s0, 1)
    }

    {
      val Value(c2) ~ Value(s2, s1, s0) = add3(Value(1, 0, 1) :: Value(1, 1, 1) :: Nil)
      assertEquals(c2, 1)
      assertEquals(s2, 1)
      assertEquals(s1, 0)
      assertEquals(s0, 0)
    }
  }

  @Test def filter(): Unit = {
    val a = variable[Vec[8]]("a")
    val circuit = Filter.movingAverage(a)
    val avg = interpret(List(a), circuit)

    // println(show(phases.flatten(phases.lift(circuit))))
    writeFile("verilog/filter.v", phases.toVerilog("Filter", List(a), circuit))

    val o1 = avg(10.toValue(8) :: Nil)
    assertEquals(o1.toInt, 2)

    val o2 = avg(20.toValue(8) :: Nil)
    assertEquals(o2.toInt, 10)

    val o3 = avg(20.toValue(8) :: Nil)
    assertEquals(o3.toInt, 17)
  }

  @Test def arithmetic(): Unit = {
    val a = variable[Vec[8]]("a")
    val b = variable[Vec[4]]("b")
    val circuit = a << b
    val shift = interpret(List(a, b), circuit)


    writeFile("verilog/shift.v", toVerilog("Shift", List(a, b), circuit))

    val o1 = shift(1.toValue(8) :: 1.toValue(4) :: Nil)
    assertEquals(o1.toInt, 2)

    val o2 = shift(2.toValue(8) :: 2.toValue(4) :: Nil)
    assertEquals(o2.toInt, 8)
  }

  def writeFile(path: String, content: String): Unit = {
    import java.io.PrintWriter

    new PrintWriter(path) {
      write(content)
      close
    }
  }
}