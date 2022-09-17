package isabelle2scala

import de.unruh.isabelle.pure.Proofterm.PThm
import Globals.ctxt
import de.unruh.isabelle.pure.Proofterm
import scala.collection.mutable

import scala.concurrent.ExecutionContext.Implicits.given
import Globals.given

//noinspection UnstableApiUsage
object Theorems {
  type Serial = Long

  def count: Int = serialMap.size

  def namedCount: Int = nameMap.size

  private val serialMap = mutable.HashMap[Serial, Theorem]()
  private val nameMap = mutable.HashMap[String, Serial]()

  def compute(pthm: PThm): Theorem = serialMap.get(pthm.header.serial) match {
    case Some(theorem) => theorem
    case None =>
      val theorem = actuallyCompute(pthm)
      serialMap.put(pthm.header.serial, theorem) match {
        case None =>
        case Some(_) =>
          throw new RuntimeException("serial already there")
      }
      if (pthm.header.name != "") {
        nameMap.get(pthm.header.name) match {
          case Some(old) =>
            val oldProp = serialMap(old).pthm.header.prop
            val prop = pthm.header.prop
            println(s"*** isabelle2scala.Theorem ${pthm.header.name} already encountered ***")
            println(s"  $old: ${oldProp.pretty(ctxt)}")
            println(s"  ${pthm.header.serial}: ${prop.pretty(ctxt)}")
            if (prop != oldProp)
              println("  Propositions differ!")
          case None =>
            nameMap.put(pthm.header.name, pthm.header.serial)
        }
      }
      theorem
  }

  def actuallyCompute(pthm: PThm): Theorem = {
    println(s"Computing: ${pthm.header.name}@${pthm.header.serial}")
    println(s"  Proposition: ${pthm.header.prop.pretty(ctxt)}")
    val proof = pthm.fullProof(ctxt.theoryOf)
    println(s"  Proof: ${proofToString(proof)}")
    isabelle2scala.Theorem(pthm = pthm)
  }

  def proofToString(proof: Proofterm): String = proof match {
    case Proofterm.MinProof => "_"
    case Proofterm.AppP(proof1, proof2) => s"AppP(${proofToString(proof1)},${proofToString(proof2)})"
    case Proofterm.Appt(proof, term) => s"Appt(${proofToString(proof)}, ${term.map(_.pretty(ctxt))}"
    case Proofterm.AbsP(name, term, proof) => s"AbsP($name, ${term.map(_.pretty(ctxt))}, ${proofToString(proof)}"
    case Proofterm.Abst(name, typ, proof) => s"Abst($name, ${typ.map(_.pretty(ctxt))}, ${proofToString(proof)}"
    case Proofterm.Hyp(term) => s"Hyp(${term.pretty(ctxt)}"
    case Proofterm.PAxm(name, prop, typ) =>
      val axiom = Axioms.compute(name, prop)
      s"$axiom(${typ.map(_.map(_.pretty(ctxt)))})"
    case Proofterm.PBound(index) => s"PBound($index)"
    case Proofterm.OfClass(typ, clazz) => s"OfClass(${typ.pretty(ctxt)}, $clazz)"
    case Proofterm.Oracle(name, term, typ) => s"Oracle($name, ${term.pretty(ctxt)}, ${typ.map(_.map(_.pretty(ctxt)))}"
    case pthm: PThm =>
      val theorem = Theorems.compute(pthm)
      theorem.toString
  }
}
