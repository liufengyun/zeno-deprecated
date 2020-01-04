import chisel3._
import chisel3.util._

class MovingAverage3 extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(8.W))
    val out = Output(UInt(8.W))
  })

  val z1 = RegNext(io.in)
  val z2 = RegNext(z1)

  io.out := (io.in + (z1 << 1.U) + z2) >> 2.U
}

object Main {
  def main(args: Array[String]): Unit = {
    val code = Driver.emitVerilog(new MovingAverage3)
    writeFile("../verilog/chisel-filter.v", code)
  }

  def writeFile(path: String, content: String): Unit = {
    import java.io.PrintWriter

    new PrintWriter(path) {
      write(content)
      close
    }
  }
}