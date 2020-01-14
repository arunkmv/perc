package freechips.rocketchip.tile

import Chisel._
import chipsalliance.rocketchip.config.Parameters
import chisel3.experimental.chiselName
import chisel3.withClock
import freechips.rocketchip.rocket.RocketCoreParams
import freechips.rocketchip.util.{ClockGate, ShouldBeRetimed, _}

import scala.collection.mutable.ArrayBuffer

case class FPUParams(
                      pLen: Int = 64,
                      divSqrt: Boolean = true,
                      sfmaLatency: Int = 3,
                      dfmaLatency: Int = 4
                    )

case class PType(es: Int, ps: Int) {
  val totalBits = ps
  val NaR = math.pow(2, totalBits - 1).toInt

  def classify(x: UInt): UInt = {
    val sign = x(totalBits - 1)
    val isZero = x === 0.U
    val isNaR = x === NaR.U

    Cat(isZero, isNaR, sign)
  }
}

object PType {
  val S = new PType(2, 32)
  val D = new PType(3, 64)

  val all = List(S, D)
}

trait HasPositFPUParameters {
  require(fLen == 0 || PType.all.exists(_.totalBits == fLen))
  val fLen: Int

  def xLen: Int

  val minXLen = 32
  val nIntTypes = log2Ceil(xLen / minXLen) + 1
  val positTypes = PType.all.filter(_.totalBits <= fLen)

  def minType = positTypes.head

  def maxType = positTypes.last

  def prevType(t: PType) = positTypes(typeTag(t) - 1)

  def maxES = maxType.es

  def maxPS = maxType.ps

  def typeTag(t: PType) = positTypes.indexOf(t)

  def sanitize(x: UInt, tag: UInt): UInt = {
    val sanitizedValues = ArrayBuffer[UInt]()
    for (inType <- positTypes) {
      sanitizedValues :+ x(inType.totalBits - 1, 0)
    }
    sanitizedValues(tag)
  }
}

abstract class PositFPUModule(implicit p: Parameters) extends CoreModule()(p) with HasPositFPUParameters

class PAToInt(implicit p: Parameters) extends PositFPUModule()(p) with ShouldBeRetimed {

  class Output extends Bundle {
    val in = new FPInput
    val lt = Bool()
    val store = Bits(width = fLen)
    val toint = Bits(width = xLen)
    val exc = Bits(width = FPConstants.FLAGS_SZ)

    override def cloneType = new Output().asInstanceOf[this.type]
  }

  val io = new Bundle {
    val in = Valid(new FPInput).flip
    val out = Valid(new Output)
  }

  val in = RegEnable(io.in.bits, io.in.valid)
  val valid = Reg(next = io.in.valid)

  val dcmp = Module(new hardposit.PositCompare(maxPS, maxES))
  dcmp.io.num1 := in.in1
  dcmp.io.num2 := in.in2

  val tag = !in.singleOut // TODO typeTag
  val store = in.in1
  val toint = Wire(init = store)
  val intType = Wire(init = tag)
  io.out.bits.store := (positTypes.map(t => Fill(maxType.totalBits / t.totalBits, store(t.totalBits - 1, 0))): Seq[UInt]) (tag)
  io.out.bits.toint := ((0 until nIntTypes).map(i => toint((minXLen << i) - 1, 0).sextTo(xLen)): Seq[UInt]) (intType)
  io.out.bits.exc := Bits(0)

  when(in.rm(0)) {
    val classify_out = (positTypes.map(t => t.classify(in.in1)): Seq[UInt]) (tag)
    toint := classify_out | (store >> minXLen << minXLen)
    intType := 0.B
  }

  when(in.wflags) {
    toint := (~in.rm & Cat(dcmp.io.lt, dcmp.io.eq)).orR | (store >> minXLen << minXLen)
    io.out.bits.exc := 0.U
    intType := 0.B

    when(!in.ren2) {
      val cvtType = in.typ.extract(log2Ceil(nIntTypes), 1)
      intType := cvtType

      for (i <- 0 until nIntTypes - 1) {
        val w = minXLen << i
        when(cvtType === i.U) {
          val conv = Module(new hardposit.PtoIConverter(maxPS, maxES, w))
          conv.io.posit := in.in1
          conv.io.unsignedOut := in.typ(0)
          toint := conv.io.integer
        }
      }
    }
  }

  io.out.valid := valid
  io.out.bits.lt := dcmp.io.lt || (dcmp.io.num1.asSInt < 0.S && dcmp.io.num2.asSInt >= 0.S)
  io.out.bits.in := in
}

class IntToPA(val latency: Int)(implicit p: Parameters) extends PositFPUModule()(p) with ShouldBeRetimed {
  val io = new Bundle {
    val in = Valid(new IntToFPInput).flip
    val out = Valid(new FPResult)
  }

  val in = Pipe(io.in)
  val tag = !in.bits.singleIn // TODO typeTag

  val mux = Wire(new FPResult)
  mux.exc := Bits(0)
  mux.data := in.bits.in1

  val intValue = {
    val res = Wire(init = in.bits.in1.asSInt)
    for (i <- 0 until nIntTypes - 1) {
      val smallInt = in.bits.in1((minXLen << i) - 1, 0)
      when(in.bits.typ.extract(log2Ceil(nIntTypes), 1) === i.U) {
        res := Mux(in.bits.typ(0), smallInt.zext, smallInt.asSInt)
      }
    }
    res.asUInt
  }

  when(in.bits.wflags) { // fcvt
    val i2pResults = for (t <- positTypes) yield {
      val conv = Module(new hardposit.ItoPConverter(t.totalBits, t.es, xLen))
      conv.io.integer := intValue
      conv.io.unsignedIn := in.bits.typ(0)
      conv.io.posit
    }

    val resultPadded = i2pResults.init.map(r => Cat(i2pResults.last >> r.getWidth, r)) :+ i2pResults.last
    mux.data := resultPadded(tag)
  }

  io.out <> Pipe(in.valid, mux, latency - 1)
}

class PAtoPA(val latency: Int)(implicit p: Parameters) extends PositFPUModule()(p) with ShouldBeRetimed {
  val io = new Bundle {
    val in = Valid(new FPInput).flip
    val out = Valid(new FPResult)
    val lt = Bool(INPUT) // from PAToInt
  }

  val fsgnj = Wire(UInt(fLen.W))

  val in = Pipe(io.in)
  for (inType <- positTypes) {
    when(inTag === typeTag(inType).B) {
      val signNum = Mux(in.bits.rm(1), in.bits.in1 ^ in.bits.in2, Mux(in.bits.rm(0), ~in.bits.in2, in.bits.in2))
      fsgnj := Mux(signNum(inType.totalBits - 1) ^ in.bits.in1(inType.totalBits - 1), ~in.bits.in1(inType.totalBits - 1, 0) + 1.U, in.bits.in1(inType.totalBits - 1, 0))
    }
  }

  val fsgnjMux = Wire(new FPResult)
  fsgnjMux.exc := UInt(0)
  fsgnjMux.data := fsgnj

  when(in.bits.wflags) { // fmin/fmax
    fsgnjMux.data := Mux(in.bits.rm(0) =/= io.lt, in.bits.in1, in.bits.in2)
  }

  val inTag = !in.bits.singleIn
  val outTag = !in.bits.singleOut
  val mux = Wire(init = fsgnjMux)
  mux := fsgnjMux

  when(in.bits.wflags && !in.bits.ren2) { // fcvt
    if (positTypes.size > 1) {
      for (outType <- positTypes) {
        for (inType <- positTypes) {
          if (typeTag(outType) != typeTag(inType)) {
            when(outTag === typeTag(outType).U && inTag === typeTag(inType).U) {
              val conv = Module(new hardposit.PtoPConverter(inType.totalBits, inType.es, outType.totalBits, outType.es))
              conv.io.in := in.bits.in1
              mux.data := conv.io.out
            }
          }
        }
      }
    }
  }
  io.out <> Pipe(in.valid, mux, latency - 1)
}

@chiselName
class PositFPU(cfg: FPUParams)(implicit p: Parameters) extends PositFPUModule()(p) {
  val io = new FPUIO

  //Gated Clock
  val useClockGating = coreParams match {
    case r: RocketCoreParams => r.clockGate
    case _ => false
  }
  val clock_en_reg = Reg(Bool())
  val clock_en = clock_en_reg || io.cp_req.valid
  val gated_clock =
    if (!useClockGating) clock
    else ClockGate(clock, clock_en, "fpu_clock_gate")

  //Decode instruction
  val fp_decoder = Module(new FPUDecoder)
  fp_decoder.io.inst := io.inst
  val id_ctrl = fp_decoder.io.sigs

  //Execute
  val ex_reg_valid = Reg(next = io.valid, init = Bool(false))
  val ex_reg_inst = RegEnable(io.inst, io.valid)
  val ex_reg_ctrl = RegEnable(id_ctrl, io.valid)
  val ex_ra = List.fill(3)(Reg(UInt()))

  // load response
  val load_wb = Reg(next = io.dmem_resp_val)
  val load_wb_double = RegEnable(io.dmem_resp_type(0), io.dmem_resp_val)
  val load_wb_data = RegEnable(io.dmem_resp_data, io.dmem_resp_val)
  val load_wb_tag = RegEnable(io.dmem_resp_tag, io.dmem_resp_val)

  @chiselName
  class PositFPUImpl { // entering gated-clock domain

    val req_valid = ex_reg_valid || io.cp_req.valid
    val ex_cp_valid = io.cp_req.fire()
    val mem_cp_valid = Reg(next = ex_cp_valid, init = Bool(false))
    val wb_cp_valid = Reg(next = mem_cp_valid, init = Bool(false))
    val mem_reg_valid = RegInit(false.B)
    val killm = (io.killm || io.nack_mem) && !mem_cp_valid
    // Kill X-stage instruction if M-stage is killed.  This prevents it from
    // speculatively being sent to the div-sqrt unit, which can cause priority
    // inversion for two back-to-back divides, the first of which is killed.
    val killx = io.killx || mem_reg_valid && killm
    mem_reg_valid := ex_reg_valid && !killx || ex_cp_valid
    val mem_reg_inst = RegEnable(ex_reg_inst, ex_reg_valid)
    val wb_reg_valid = Reg(next = mem_reg_valid && (!killm || mem_cp_valid), init = Bool(false))

    val cp_ctrl = Wire(new FPUCtrlSigs)
    cp_ctrl <> io.cp_req.bits
    io.cp_resp.valid := Bool(false)
    io.cp_resp.bits.data := UInt(0)

    val ex_ctrl = Mux(ex_cp_valid, cp_ctrl, ex_reg_ctrl)
    val mem_ctrl = RegEnable(ex_ctrl, req_valid)
    val wb_ctrl = RegEnable(mem_ctrl, mem_reg_valid)

    // regfile
    val regfile = Mem(32, Bits(width = fLen + 1))
    when(load_wb) {
      val wdata = sanitize(load_wb_data, load_wb_double)
      regfile(load_wb_tag) := wdata
      if (enableCommitLog)
        printf("f%d p%d 0x%x\n", load_wb_tag, load_wb_tag + 32.U, load_wb_data)
    }

    // Selecting source registers
    val ex_rs = ex_ra.map(a => regfile(a))
    when(io.valid) {
      when(id_ctrl.ren1) {
        when(!id_ctrl.swap12) {
          ex_ra(0) := io.inst(19, 15)
        }
        when(id_ctrl.swap12) {
          ex_ra(1) := io.inst(19, 15)
        }
      }
      when(id_ctrl.ren2) {
        when(id_ctrl.swap12) {
          ex_ra(0) := io.inst(24, 20)
        }
        when(id_ctrl.swap23) {
          ex_ra(2) := io.inst(24, 20)
        }
        when(!id_ctrl.swap12 && !id_ctrl.swap23) {
          ex_ra(1) := io.inst(24, 20)
        }
      }
      when(id_ctrl.ren3) {
        ex_ra(2) := io.inst(31, 27)
      }
    }
    val ex_rm = 0.U //Posit supports only 1 rounding mode(RNE) TODO Tie fcsr_rm to ground

    def fuInput(minT: Option[FType]): FPInput = {
      val req = Wire(new FPInput)
      val tag = !ex_ctrl.singleIn // TODO typeTag
      req := ex_ctrl
      req.rm := ex_rm
      req.in1 := sanitize(ex_rs(0), tag)
      req.in2 := sanitize(ex_rs(1), tag)
      req.in3 := sanitize(ex_rs(2), tag)
      req.typ := ex_reg_inst(21, 20)
      req.fmaCmd := ex_reg_inst(3, 2) | (!ex_ctrl.ren3 && ex_reg_inst(27))
      when(ex_cp_valid) {
        req := io.cp_req.bits
        when(io.cp_req.bits.swap23) {
          req.in2 := io.cp_req.bits.in3
          req.in3 := io.cp_req.bits.in2
        }
      }
      req
    }
  }

  val fpuImpl = withClock(gated_clock) {
    new PositFPUImpl
  }
}

