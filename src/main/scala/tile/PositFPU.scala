package freechips.rocketchip.tile

import Chisel.ImplicitConversions._
import Chisel._
import chipsalliance.rocketchip.config.Parameters
import chisel3.experimental.chiselName
import chisel3.internal.sourceinfo.SourceInfo
import chisel3.withClock
import freechips.rocketchip.rocket.RocketCoreParams
import freechips.rocketchip.util.property.cover
import freechips.rocketchip.util.{ClockGate, ShouldBeRetimed, _}

import scala.collection.mutable.ArrayBuffer

case class PFPUParams(
                       pLen: Int = 64,
                       divSqrt: Boolean = true,
                       fmaLatency: Int = 2
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
    val sanitizedValues = positTypes.map(t => x(t.totalBits - 1, 0))
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
  dcmp.io.num1 := in.in1.asSInt()
  dcmp.io.num2 := in.in2.asSInt()

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
    when(!in.bits.singleIn === typeTag(inType).B) {
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

class PFPUFMAPipe(val latency: Int, val t: PType)
                 (implicit p: Parameters) extends FPUModule()(p) with ShouldBeRetimed {
  require(latency > 0)

  val io = new Bundle {
    val in = Valid(new FPInput).flip
    val out = Valid(new FPResult)
  }

  val in = Reg(new FPInput)
  when(io.in.valid) {
    val one = UInt(1) << (t.totalBits - 2)
    val zero = 0.U
    val cmd_fma = io.in.bits.ren3
    val cmd_addsub = io.in.bits.swap23
    in := io.in.bits
    when(cmd_addsub) {
      in.in2 := one
    }
    when(!(cmd_fma || cmd_addsub)) {
      in.in3 := zero
    }
  }

  val fma = Module(new hardposit.PositFMA(t.totalBits, t.es))
  fma.io.num1 := in.in1
  fma.io.num2 := in.in2
  fma.io.num3 := in.in3
  fma.io.negate := in.fmaCmd(1)
  fma.io.sub := in.fmaCmd(0)

  val res = Wire(new FPResult)
  res.data := fma.io.out
  res.exc := 0.U

  io.out := Pipe(io.in.valid, res, (latency - 1) max 0)
}

@chiselName
class PositFPU(cfg: PFPUParams)(implicit p: Parameters) extends PositFPUModule()(p) {
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

    def fuInput: FPInput = {
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

    val sfma = Module(new PFPUFMAPipe(cfg.fmaLatency, PType.S))
    sfma.io.in.valid := req_valid && ex_ctrl.fma && ex_ctrl.singleOut
    sfma.io.in.bits := fuInput

    val paiu = Module(new PAToInt)
    paiu.io.in.valid := req_valid && (ex_ctrl.toint || ex_ctrl.div || ex_ctrl.sqrt || (ex_ctrl.fastpipe && ex_ctrl.wflags))
    paiu.io.in.bits := fuInput
    io.store_data := paiu.io.out.bits.store
    io.toint_data := paiu.io.out.bits.toint
    when(paiu.io.out.valid && mem_cp_valid && mem_ctrl.toint) {
      io.cp_resp.bits.data := paiu.io.out.bits.toint
      io.cp_resp.valid := Bool(true)
    }

    val ipau = Module(new IntToPA(latency = 2))
    ipau.io.in.valid := req_valid && ex_ctrl.fromint
    ipau.io.in.bits := paiu.io.in.bits
    ipau.io.in.bits.in1 := Mux(ex_cp_valid, io.cp_req.bits.in1, io.fromint_data)

    val pamu = Module(new PAtoPA(2))
    pamu.io.in.valid := req_valid && ex_ctrl.fastpipe
    pamu.io.in.bits := paiu.io.in.bits
    pamu.io.lt := paiu.io.out.bits.lt

    val divSqrt_wen = Wire(init = false.B)
    val divSqrt_inFlight = Wire(init = false.B)
    val divSqrt_waddr = Reg(UInt(width = 5))
    val divSqrt_typeTag = Wire(UInt(width = log2Up(positTypes.size)))
    val divSqrt_wdata = Wire(UInt(width = fLen)) // TODO add PLen
    val divSqrt_flags = Wire(UInt(width = FPConstants.FLAGS_SZ))

    // writeback arbitration
    case class Pipe(p: Module, lat: Int, cond: (FPUCtrlSigs) => Bool, res: FPResult)

    val pipes = List(
      Pipe(pamu, pamu.latency, (c: FPUCtrlSigs) => c.fastpipe, pamu.io.out.bits),
      Pipe(ipau, ipau.latency, (c: FPUCtrlSigs) => c.fromint, ipau.io.out.bits),
      Pipe(sfma, sfma.latency, (c: FPUCtrlSigs) => c.fma && c.singleOut, sfma.io.out.bits)) ++
      (fLen > 32).option({
        val dfma = Module(new FPUFMAPipe(cfg.fmaLatency, FType.D))
        dfma.io.in.valid := req_valid && ex_ctrl.fma && !ex_ctrl.singleOut
        dfma.io.in.bits := fuInput
        Pipe(dfma, dfma.latency, (c: FPUCtrlSigs) => c.fma && !c.singleOut, dfma.io.out.bits)
      })

    def latencyMask(c: FPUCtrlSigs, offset: Int) = {
      require(pipes.forall(_.lat >= offset))
      pipes.map(p => Mux(p.cond(c), UInt(1 << p.lat - offset), UInt(0))).reduce(_ | _)
    }

    def pipeid(c: FPUCtrlSigs) = pipes.zipWithIndex.map(p => Mux(p._1.cond(c), UInt(p._2), UInt(0))).reduce(_ | _)

    val maxLatency = pipes.map(_.lat).max
    val memLatencyMask = latencyMask(mem_ctrl, 2)

    class WBInfo extends Bundle {
      val rd = UInt(width = 5)
      val single = Bool()
      val cp = Bool()
      val pipeid = UInt(width = log2Ceil(pipes.size))

      override def cloneType: this.type = new WBInfo().asInstanceOf[this.type]
    }

    val wen = Reg(init = Bits(0, maxLatency - 1))
    val wbInfo = Reg(Vec(maxLatency - 1, new WBInfo))
    val mem_wen = mem_reg_valid && (mem_ctrl.fma || mem_ctrl.fastpipe || mem_ctrl.fromint)
    val write_port_busy = RegEnable(mem_wen && (memLatencyMask & latencyMask(ex_ctrl, 1)).orR || (wen & latencyMask(ex_ctrl, 0)).orR, req_valid)
    ccover(mem_reg_valid && write_port_busy, "WB_STRUCTURAL", "structural hazard on writeback")

    for (i <- 0 until maxLatency - 2) {
      when(wen(i + 1)) {
        wbInfo(i) := wbInfo(i + 1)
      }
    }
    wen := wen >> 1
    when(mem_wen) {
      when(!killm) {
        wen := wen >> 1 | memLatencyMask
      }
      for (i <- 0 until maxLatency - 1) {
        when(!write_port_busy && memLatencyMask(i)) {
          wbInfo(i).cp := mem_cp_valid
          wbInfo(i).single := mem_ctrl.singleOut
          wbInfo(i).pipeid := pipeid(mem_ctrl)
          wbInfo(i).rd := mem_reg_inst(11, 7)
        }
      }
    }

    val waddr = Mux(divSqrt_wen, divSqrt_waddr, wbInfo(0).rd)
    val wdouble = Mux(divSqrt_wen, divSqrt_typeTag, !wbInfo(0).single)
    val wdata = Mux(divSqrt_wen, divSqrt_wdata, (pipes.map(_.res.data): Seq[UInt]) (wbInfo(0).pipeid))
    val wexc = (pipes.map(_.res.exc): Seq[UInt]) (wbInfo(0).pipeid)
    when((!wbInfo(0).cp && wen(0)) || divSqrt_wen) {
      regfile(waddr) := wdata
      if (enableCommitLog) {
        printf("f%d p%d 0x%x\n", waddr, waddr + 32.U, wdata)
      }
    }
    when(wbInfo(0).cp && wen(0)) {
      io.cp_resp.bits.data := wdata
      io.cp_resp.valid := Bool(true)
    }
    io.cp_req.ready := !ex_reg_valid

    val wb_toint_valid = wb_reg_valid && wb_ctrl.toint
    val wb_toint_exc = RegEnable(paiu.io.out.bits.exc, mem_ctrl.toint)
    io.fcsr_flags.valid := wb_toint_valid || divSqrt_wen || wen(0)
    io.fcsr_flags.bits :=
      Mux(wb_toint_valid, wb_toint_exc, UInt(0)) |
        Mux(divSqrt_wen, divSqrt_flags, UInt(0)) |
        Mux(wen(0), wexc, UInt(0))

    val divSqrt_write_port_busy = (mem_ctrl.div || mem_ctrl.sqrt) && wen.orR
    io.fcsr_rdy := !(ex_reg_valid && ex_ctrl.wflags || mem_reg_valid && mem_ctrl.wflags || wb_reg_valid && wb_ctrl.toint || wen.orR || divSqrt_inFlight)
    io.nack_mem := write_port_busy || divSqrt_write_port_busy || divSqrt_inFlight
    io.dec <> fp_decoder.io.sigs

    def useScoreboard(f: ((Pipe, Int)) => Bool) = pipes.zipWithIndex.filter(_._1.lat > 3).map(x => f(x)).fold(Bool(false))(_ || _)

    io.sboard_set := wb_reg_valid && !wb_cp_valid && Reg(next = useScoreboard(_._1.cond(mem_ctrl)) || mem_ctrl.div || mem_ctrl.sqrt)
    io.sboard_clr := !wb_cp_valid && (divSqrt_wen || (wen(0) && useScoreboard(x => wbInfo(0).pipeid === UInt(x._2))))
    io.sboard_clra := waddr
    ccover(io.sboard_clr && load_wb, "DUAL_WRITEBACK", "load and FMA writeback on same cycle")
    // we don't currently support round-max-magnitude (rm=4)
    io.illegal_rm := io.inst(14, 12).isOneOf(5, 6) || io.inst(14, 12) === 7 && io.fcsr_rm >= 5

    if (cfg.divSqrt) {
      val divSqrt_killed = Reg(Bool())
      ccover(divSqrt_inFlight && divSqrt_killed, "DIV_KILLED", "divide killed after issued to divider")
      ccover(divSqrt_inFlight && mem_reg_valid && (mem_ctrl.div || mem_ctrl.sqrt), "DIV_BUSY", "divider structural hazard")
      ccover(mem_reg_valid && divSqrt_write_port_busy, "DIV_WB_STRUCTURAL", "structural hazard on division writeback")

      for (t <- positTypes) {
        val tag = !mem_ctrl.singleOut // TODO typeTag
        val divSqrt = Module(new hardposit.PositDivSqrt(t.totalBits, t.es))
        divSqrt.io.validIn := mem_reg_valid && tag === typeTag(t) && (mem_ctrl.div || mem_ctrl.sqrt) && !divSqrt_inFlight
        divSqrt.io.sqrtOp := mem_ctrl.sqrt
        divSqrt.io.num1 := paiu.io.out.bits.in.in1
        divSqrt.io.num2 := paiu.io.out.bits.in.in2

        when(!divSqrt.io.readyIn) {
          divSqrt_inFlight := true
        } // only 1 in flight

        when(divSqrt.io.validIn && divSqrt.io.readyIn) {
          divSqrt_killed := killm
          divSqrt_waddr := mem_reg_inst(11, 7)
        }

        when(divSqrt.io.validOut_div || divSqrt.io.validOut_sqrt) {
          divSqrt_wen := !divSqrt_killed
          divSqrt_wdata := divSqrt.io.out
          divSqrt_flags := divSqrt.io.exceptions
          divSqrt_typeTag := typeTag(t)
        }
      }
    } else {
      when(id_ctrl.div || id_ctrl.sqrt) {
        io.illegal_rm := true
      }
    }

    // gate the clock
    clock_en_reg := !useClockGating ||
      io.keep_clock_enabled || // chicken bit
      io.valid || // ID stage
      req_valid || // EX stage
      mem_reg_valid || mem_cp_valid || // MEM stage
      wb_reg_valid || wb_cp_valid || // WB stage
      wen.orR || divSqrt_inFlight || // post-WB stage
      io.dmem_resp_val // load writeback
  } // leaving gated-clock domain

  val pfpuImpl = withClock(gated_clock) {
    new PositFPUImpl
  }

  def ccover(cond: Bool, label: String, desc: String)(implicit sourceInfo: SourceInfo) =
    cover(cond, s"FPU_$label", "Core;;" + desc)
}

