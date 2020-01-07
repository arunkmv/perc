package freechips.rocketchip.tile

import Chisel._
import chipsalliance.rocketchip.config.Parameters
import chisel3.experimental.chiselName
import chisel3.withClock
import freechips.rocketchip.rocket.RocketCoreParams
import freechips.rocketchip.util.{ClockGate, ShouldBeRetimed, _}

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

      val w = minXLen << cvtType
      val conv = Module(new hardposit.PtoIConverter(maxPS, maxES, w))
      conv.io.posit := in.in1
      conv.io.unsigned := in.typ(0)
      toint := conv.io.integer
    }
  }

  io.out.valid := valid
  io.out.bits.lt := dcmp.io.lt || (dcmp.io.num1.asSInt < 0.S && dcmp.io.num2.asSInt >= 0.S)
  io.out.bits.in := in
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
      val wdata = recode(load_wb_data, load_wb_double)
      regfile(load_wb_tag) := wdata
      assert(consistent(wdata))
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


  }

  val fpuImpl = withClock(gated_clock) {
    new PositFPUImpl
  }
}

