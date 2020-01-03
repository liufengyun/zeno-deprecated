package ysm

import org.junit.Test
import org.junit.Assert._

import java.nio.charset.StandardCharsets._
import java.nio.file.{Files, Paths, FileSystems, Path}
import java.io.File

import lang._

import scala.language.implicitConversions
class TestSuite {
  @Test def controller(): Unit = {
    var  success: Boolean = true

    val path = new java.io.File("asm")
    path.listFiles.filter(f => f.isFile && f.getName.endsWith(".s")).foreach { f =>
      val res =  Controller.test(f.toString)

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

    // run all tests by default
    assertTrue(success)
  }

  @Test def adder2(): Unit = {
    val a = variable[Vec[2]]("a")
    val b = variable[Vec[2]]("b")
    val circuit = Adder.adder2(a, b)
    val add2 = phases.interpret(List(a, b), circuit)

    {
      val Bits(c1, s1, s0) = add2(Bits(1, 0) :: Bits(0, 1) :: Nil)
      assertEquals(c1, 0)
      assertEquals(s1, 1)
      assertEquals(s0, 1)
    }

    {
      val Bits(c1, s1, s0) = add2(Bits(1, 0) :: Bits(1, 1) :: Nil)
      assertEquals(c1, 1)
      assertEquals(s1, 0)
      assertEquals(s0, 1)
    }
  }

  @Test def adderN(): Unit = {
    val a = variable[Vec[3]]("a")
    val b = variable[Vec[3]]("b")
    val circuit = Adder.adderN(a, b)
    val add3 = phases.interpret(List(a, b), circuit)

    {
      val Bits(c2) ~ Bits(s2, s1, s0) = add3(Bits(1, 0, 1) :: Bits(0, 1, 0) :: Nil)
      assertEquals(c2, 0)
      assertEquals(s2, 1)
      assertEquals(s1, 1)
      assertEquals(s0, 1)
    }

    {
      val Bits(c2) ~ Bits(s2, s1, s0) = add3(Bits(1, 0, 1) :: Bits(1, 1, 1) :: Nil)
      assertEquals(c2, 1)
      assertEquals(s2, 1)
      assertEquals(s1, 0)
      assertEquals(s0, 0)
    }
  }
}