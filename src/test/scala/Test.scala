package ysm

import org.junit.Test
import org.junit.Assert._

import java.nio.charset.StandardCharsets._
import java.nio.file.{Files, Paths, FileSystems, Path}
import java.io.File

import lang._

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

  @Test def adder(): Unit = {
    val a = variable[Vec[2]]("a")
    val b = variable[Vec[2]]("b")
    val circuit = examples.adder2(a, b)
    val add2 = phases.interpret(List(a, b), circuit)
    val c ~ VecV(bit1, bit2) = add2(VecV(1, 0) :: Nil)
  }
}