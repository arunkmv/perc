package freechips.rocketchip.tile

import Chisel.ImplicitConversions._
import Chisel._
import chipsalliance.rocketchip.config.Parameters
import chisel3.experimental.chiselName
import chisel3.internal.sourceinfo.SourceInfo
import chisel3.util.MixedVec
import chisel3.withClock
import freechips.rocketchip.rocket.RocketCoreParams
import freechips.rocketchip.util.property.cover
import freechips.rocketchip.util.{ClockGate, ShouldBeRetimed, _}

sealed trait FPUType
case object IEEE754 extends FPUType
case object POSIT   extends FPUType

class unPackedToGenerator(val totalBits: Int, val es: Int) extends Bundle with hardposit.HasHardPositParams {
  val unpackedPosit = new hardposit.unpackedPosit(totalBits, es)
  val trailingBits = UInt(trailingBitCount.W)
  val stickyBit = Bool()
}

class PFPUIO(implicit p: Parameters) extends FPUCoreIO ()(p) {
  val cp_req = Decoupled(new PAInput()).flip //cp doesn't pay attn to kill sigs
  val cp_resp = Decoupled(new PAResult())
}

class PAResult(implicit p: Parameters) extends CoreBundle()(p) with HasPositFPUParameters {
  val data = Bits(width = fLen)
  val exc = Bits(width = FPConstants.FLAGS_SZ)
  val useGen = Bool()
  val genTag = Bool()
  val dataToGenerator = MixedVec(positTypes.map(t => new unPackedToGenerator(t.totalBits, t.es)))
}

class FMAPipeInput(val t: PType) (implicit p: Parameters) extends CoreBundle()(p) with HasFPUCtrlSigs with HasPositFPUParameters {
  val rm = Bits(width = FPConstants.RM_SZ)
  val fmaCmd = Bits(width = 2)
  val inExtr = Vec(3, new hardposit.unpackedPosit(t.totalBits, t.es))
}

class IntToPAInput(implicit p: Parameters) extends CoreBundle()(p) with HasFPUCtrlSigs with HasPositFPUParameters {
  val rm = Bits(width = FPConstants.RM_SZ)
  val typ = Bits(width = 2)
  val in1 = Bits(width = xLen)
  val in1Extr = MixedVec(positTypes.map(t => new hardposit.unpackedPosit(t.totalBits, t.es)))
}

class PAInput(implicit p: Parameters) extends CoreBundle()(p) with HasFPUCtrlSigs with HasPositFPUParameters {
  val rm = Bits(width = FPConstants.RM_SZ)
  val fmaCmd = Bits(width = 2)
  val typ = Bits(width = 2)
  val in1 = Bits(width = fLen)
  val in2 = Bits(width = fLen)
  val in3 = Bits(width = fLen)
  val inExtr = MixedVec(positTypes.map(t => Vec(3, new hardposit.unpackedPosit(t.totalBits, t.es))))

  override def cloneType = new PAInput().asInstanceOf[this.type]
}


case class PType(es: Int, ps: Int) extends hardposit.HasHardPositParams {
  val totalBits = ps

  def classify(x: UInt): UInt = {
    val sign = x(totalBits - 1)
    val is_zero = isZero(x)
    val is_NaR = isNaR(x)

    Cat(is_zero, is_NaR, Mux(is_NaR, 0.U, sign))
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
    val in = new PAInput
    val lt = Bool()
    val store = Bits(width = fLen)
    val toint = Bits(width = xLen)
    val exc = Bits(width = FPConstants.FLAGS_SZ)

    override def cloneType = new Output().asInstanceOf[this.type]
  }

  val io = new Bundle {
    val in = Valid(new PAInput).flip
    val out = Valid(new Output)
  }

  val in = RegEnable(io.in.bits, io.in.valid)
  val valid = Reg(next = io.in.valid)

  val inTag = !in.singleIn // TODO typeTag
  val outTag = !in.singleOut
  val store = in.in1

  val cmpIn1 = Wire(UInt(maxPS.W))
  val cmpIn2 = Wire(UInt(maxPS.W))

  for(p <- positTypes) {
    when(inTag === typeTag(p)) {
      cmpIn1 := in.in1(p.ps - 1, 0).sextTo(maxPS)
      cmpIn2 := in.in2(p.ps - 1, 0).sextTo(maxPS)
    }
  }

  val dcmp = Module(new hardposit.PositCompare(maxPS, maxES))
  dcmp.io.num1 := cmpIn1.asSInt()
  dcmp.io.num2 := cmpIn2.asSInt()

  val toint = Wire(init = store)
  val intType = Wire(init = outTag)
  io.out.bits.store := (positTypes.map(t => Fill(maxType.totalBits / t.totalBits, store(t.totalBits - 1, 0))): Seq[UInt]) (outTag)
  io.out.bits.toint := ((0 until nIntTypes).map(i => toint((minXLen << i) - 1, 0).sextTo(xLen)): Seq[UInt]) (intType)
  io.out.bits.exc := Bits(0)

  when(in.rm(0)) {
    val classify_out = (positTypes.map(t => t.classify(in.in1)): Seq[UInt]) (inTag)
    toint := classify_out | (store >> minXLen << minXLen)
    intType := 0.B
  }

  when(in.wflags) {
    toint := (~in.rm & Cat(dcmp.io.lt, dcmp.io.eq)).orR | (store >> minXLen << minXLen)
    io.out.bits.exc := 0.U
    intType := 0.B

    when(!in.ren2) {
      intType := in.typ.extract(log2Ceil(nIntTypes), 1)

      for (i <- 0 until nIntTypes) {
        for (p <- positTypes) {
          val w = minXLen << i
          when(intType === i.U && inTag === typeTag(p).U) {
            val conv = Module(new hardposit.PtoIConverterCore(p.ps, p.es, w))
            conv.io.posit := in.inExtr(typeTag(p))(0)
            conv.io.unsignedOut := in.typ(0)
            toint := conv.io.integer
          }
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
    val in = Valid(new IntToPAInput).flip
    val out = Valid(new PAResult)
  }

  val in = Pipe(io.in)
  val tag = !in.bits.singleIn // TODO typeTag

  val mux = Wire(new PAResult)
  mux.exc := Bits(0)
  mux.data := in.bits.in1
  mux.useGen := false.B

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
    for (t <- positTypes) {
      when(typeTag(t) === tag) {
        val conv = Module(new hardposit.ItoPConverterCore(t.totalBits, t.es, xLen))
        conv.io.integer := intValue
        conv.io.unsignedIn := in.bits.typ(0)
        mux.dataToGenerator(typeTag(t)).unpackedPosit := conv.io.posit
        mux.dataToGenerator(typeTag(t)).trailingBits := conv.io.trailingBits
        mux.dataToGenerator(typeTag(t)).stickyBit := conv.io.stickyBit
      }
    }
    mux.useGen := true.B
  }

  io.out <> Pipe(in.valid, mux, latency - 1)
}

class PAtoPA(val latency: Int)(implicit p: Parameters) extends PositFPUModule()(p) with ShouldBeRetimed {
  val io = new Bundle {
    val in = Valid(new PAInput).flip
    val out = Valid(new PAResult)
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

  val fsgnjMux = Wire(new PAResult)
  fsgnjMux.exc := UInt(0)
  fsgnjMux.data := fsgnj
  fsgnjMux.useGen := false.B

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
              val conv = Module(new hardposit.PtoPConverterCore(inType.totalBits, inType.es, outType.totalBits, outType.es))
              conv.io.in := in.bits.inExtr(typeTag(inType))(0)
              mux.dataToGenerator(typeTag(outType)).unpackedPosit := conv.io.out
              mux.dataToGenerator(typeTag(outType)).trailingBits := conv.io.trailingBits
              mux.dataToGenerator(typeTag(outType)).stickyBit := conv.io.stickyBit
              mux.useGen := true.B
            }
          }
        }
      }
    }
  }
  io.out <> Pipe(in.valid, mux, latency - 1)
}

class PFPUFMAPipe(val latency: Int, val t: PType)
                 (implicit p: Parameters) extends PositFPUModule()(p) with ShouldBeRetimed {
  require(latency > 0)

  val io = new Bundle {
    val in = Valid(new FMAPipeInput(t)).flip
    val out = Valid(new PAResult)
  }

  val in = Reg(new FMAPipeInput(t))
  when(io.in.valid) {
    in := io.in.bits
  }

  val fmaValid = RegNext(io.in.valid)

  val fma = Module(new hardposit.PositFMACore(t.totalBits, t.es))
  fma.io.num1 := in.inExtr(0)
  fma.io.num2 := in.inExtr(1)
  fma.io.num3 := in.inExtr(2)
  fma.io.negate := in.fmaCmd(1)
  fma.io.sub := in.fmaCmd.xorR

  val res = Wire(new PAResult)
  res.dataToGenerator(typeTag(t)).unpackedPosit := fma.io.out
  res.dataToGenerator(typeTag(t)).trailingBits := fma.io.trailingBits
  res.dataToGenerator(typeTag(t)).stickyBit := fma.io.stickyBit
  res.useGen := true.B
  res.exc := 0.U

  io.out := Pipe(fmaValid, res, (latency - 1) max 0)
}

@chiselName
class PositFPU(cfg: FPUParams)(implicit p: Parameters) extends PositFPUModule()(p) {
  val io = new PFPUIO

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
    val regfile = Mem(32, Bits(width = fLen))
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
    val ex_rm = Mux(ex_reg_inst(14,12) === Bits(7), io.fcsr_rm, ex_reg_inst(14,12)) //Posit supports only 1 rounding mode(RNE) TODO Tie fcsr_rm to ground
    val isFma = req_valid && ex_ctrl.fma
    def pfuInput: PAInput = {
      val req = Wire(new PAInput)
      val tag = !ex_ctrl.singleIn // TODO typeTag
      val isFma_addsub = isFma && ex_ctrl.swap23
      val isFma_mul = !(ex_ctrl.ren3 || isFma_addsub)
      req := ex_ctrl
      req.rm := ex_rm
      req.in1 := sanitize(ex_rs(0), tag)
      req.in2 := sanitize(ex_rs(1), tag)
      req.in3 := sanitize(ex_rs(2), tag)
      for(t <- positTypes) {
        val one = (1 << (t.totalBits - 2)).U
        val zero = 0.U

        val in1Extractor = Module(new hardposit.PositExtractor(t.totalBits, t.es))
        val in2Extractor = Module(new hardposit.PositExtractor(t.totalBits, t.es))
        val in3Extractor = Module(new hardposit.PositExtractor(t.totalBits, t.es))

        in1Extractor.io.in := req.in1
        in2Extractor.io.in := Mux(isFma_addsub, one, req.in2)
        in3Extractor.io.in := Mux(isFma_mul, zero, req.in3)

        req.inExtr(typeTag(t))(0) := in1Extractor.io.out
        req.inExtr(typeTag(t))(1) := in2Extractor.io.out
        req.inExtr(typeTag(t))(2) := in3Extractor.io.out
      }
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

    val paInput = pfuInput

    val sfma = Module(new PFPUFMAPipe(cfg.sfmaLatency, PType.S))
    sfma.io.in.valid := isFma && ex_ctrl.singleOut
    sfma.io.in.bits.rm := paInput.rm
    sfma.io.in.bits.fmaCmd := paInput.fmaCmd
    sfma.io.in.bits.inExtr := paInput.inExtr(typeTag(PType.S))

    val paiu = Module(new PAToInt)
    paiu.io.in.valid := req_valid && (ex_ctrl.toint || ex_ctrl.div || ex_ctrl.sqrt || (ex_ctrl.fastpipe && ex_ctrl.wflags))
    paiu.io.in.bits := paInput
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
    positTypes.map(t => ipau.io.in.bits.in1Extr(typeTag(t)) := paiu.io.in.bits.inExtr(typeTag(t))(0))

    val pamu = Module(new PAtoPA(2))
    pamu.io.in.valid := req_valid && ex_ctrl.fastpipe
    pamu.io.in.bits := paiu.io.in.bits
    pamu.io.lt := paiu.io.out.bits.lt

    val divSqrt_wen = Wire(init = false.B)
    val divSqrt_inFlight = Wire(init = false.B)
    val divSqrt_waddr = Reg(UInt(width = 5))
    val divSqrt_typeTag = Wire(UInt(width = log2Up(positTypes.size)))
    val divSqrt_wdata = Wire(MixedVec(positTypes.map(t => new unPackedToGenerator(t.totalBits, t.es)))) // TODO add PLen
    val divSqrt_flags = Wire(UInt(width = FPConstants.FLAGS_SZ))

    // writeback arbitration
    case class Pipe(p: Module, lat: Int, cond: (FPUCtrlSigs) => Bool, res: PAResult)

    val pipes = List(
      Pipe(pamu, pamu.latency, (c: FPUCtrlSigs) => c.fastpipe, pamu.io.out.bits),
      Pipe(ipau, ipau.latency, (c: FPUCtrlSigs) => c.fromint, ipau.io.out.bits),
      Pipe(sfma, sfma.latency, (c: FPUCtrlSigs) => c.fma && c.singleOut, sfma.io.out.bits)) ++
      (fLen > 32).option({
        val dfma = Module(new PFPUFMAPipe(cfg.dfmaLatency, PType.D))
        dfma.io.in.valid := req_valid && ex_ctrl.fma && !ex_ctrl.singleOut
        dfma.io.in.bits.rm := paInput.rm
        dfma.io.in.bits.fmaCmd := paInput.fmaCmd
        dfma.io.in.bits.inExtr := paInput.inExtr(typeTag(PType.D))
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

    val wdata = Wire(UInt(width = fLen))
    for(t <- positTypes) {
      val outGenerator = Module(new hardposit.PositGenerator(t.totalBits, t.es))
      val pipeResult = (pipes.map(_.res): Seq[PAResult]) (wbInfo(0).pipeid)
      val useGenResult = divSqrt_wen | pipeResult.useGen
      outGenerator.io.in := Mux(divSqrt_wen, divSqrt_wdata(typeTag(t)).unpackedPosit, pipeResult.dataToGenerator(typeTag(t)).unpackedPosit)
      outGenerator.io.trailingBits := Mux(divSqrt_wen, divSqrt_wdata(typeTag(t)).trailingBits, pipeResult.dataToGenerator(typeTag(t)).trailingBits)
      outGenerator.io.stickyBit := Mux(divSqrt_wen, divSqrt_wdata(typeTag(t)).stickyBit, pipeResult.dataToGenerator(typeTag(t)).stickyBit)

      when(typeTag(t) === wdouble) {
        wdata := Mux(useGenResult, outGenerator.io.out, pipeResult.data)
      }
    }

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
        val divSqrt = Module(new hardposit.PositDivSqrtCore(t.totalBits, t.es))
        divSqrt.io.validIn := mem_reg_valid && tag === typeTag(t) && (mem_ctrl.div || mem_ctrl.sqrt) && !divSqrt_inFlight
        divSqrt.io.sqrtOp := mem_ctrl.sqrt
        divSqrt.io.num1 := paiu.io.out.bits.in.inExtr(typeTag(t))(0)
        divSqrt.io.num2 := paiu.io.out.bits.in.inExtr(typeTag(t))(1)

        when(!divSqrt.io.readyIn) {
          divSqrt_inFlight := true
        } // only 1 in flight

        when(divSqrt.io.validIn && divSqrt.io.readyIn) {
          divSqrt_killed := killm
          divSqrt_waddr := mem_reg_inst(11, 7)
        }

        when(divSqrt.io.validOut_div || divSqrt.io.validOut_sqrt) {
          divSqrt_wen := !divSqrt_killed
          divSqrt_wdata(typeTag(t)).unpackedPosit := divSqrt.io.out
          divSqrt_wdata(typeTag(t)).trailingBits := divSqrt.io.trailingBits
          divSqrt_wdata(typeTag(t)).stickyBit := divSqrt.io.stickyBit
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

