package isabelle2scala2

import de.unruh.isabelle.pure.Proofterm.PThm

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.pure.{Proofterm, Term}
import isabelle2scala2.Theorem.Serial

import scala.collection.mutable.ListBuffer
import scala.concurrent.Future

//noinspection UnstableApiUsage
case class Theorem(name: String, serial: Serial, axioms: List[Axiom]) {
  override def toString: String = s"Theorem(${name}@${serial})"
}

//noinspection UnstableApiUsage
object Theorem {
  type Serial = Long

  def createTheorem(pthm: PThm, output: PrintWriter): Future[Theorem] = {
//    println(s"Working on ${pthm.header.name}")
    val name = pthm.header.name
    def prop: Term = pthm.header.prop
    val fullName: String = Naming.mapName(
      name = name, extra = pthm.header.serial,
      suggestion = if (name.nonEmpty) name else "thm_" + pthm.header.serial,
      category = Namespace.Theorem)

    val proof: Proofterm = pthm.fullProof(ctxt.theoryOf)

    val constantsBuffer = UniqueListBuffer[Constant#Instantiated]()
    val propString = Utils.translateTermClean(prop, constants = constantsBuffer)
    val propConstants = constantsBuffer.toList

    val constants = propConstants // TODO include the ones in proof
    val constsString = constants map { const =>
      val args = const.typArgs map { typ => s" (${Utils.translateTyp(typ)})" } mkString " "
      s"(${const.fullName}: ${const.constant.fullName}$args)"
    } mkString (" ")

    for (typArgString <- Utils.typArgumentsOfProp(prop);
         valArgString <- Utils.valArgumentsOfProp(prop);
         axioms <- allAxiomsInProof(proof))
    yield {


      output.synchronized {
        output.println(s"/-- Isabelle lemma ${name} (${pthm.header.serial}): ${prop.pretty(ctxt)} -/")
        output.println(s"theorem $fullName")
        if (typArgString.nonEmpty)
          output.println(s"     /- Type args -/  $typArgString")
        if (constsString.nonEmpty)
          output.println(s"     /- Constants -/  $constsString")
        if (valArgString.nonEmpty)
          output.println(s"     /- Value args -/ $valArgString")
        output.println(s"  : $propString :=")
        output.println()
        output.println(s"  sorry")
        output.println()
        output.flush()
      }

//      println(s"Done: ${pthm.header.name}")
      Theorem(name = name, serial = pthm.header.serial, axioms = axioms)
    }
  }

  def allAxiomsInProof(proof: Proofterm): Future[List[Axiom]] = {
    val axiomsBuffer = new UniqueListBuffer[Axiom]

    def findAxioms(prf: Proofterm): Unit = prf match
      case Proofterm.MinProof => ???
      case Proofterm.AppP(proof1, proof2) => findAxioms(proof1); findAxioms(proof2)
      case Proofterm.Appt(proof, term) => findAxioms(proof)
      case Proofterm.AbsP(name, term, proof) => findAxioms(proof)
      case Proofterm.Abst(name, typ, proof) => findAxioms(proof)
      case Proofterm.Hyp(term) =>
      case Proofterm.PAxm(name, term, typ) =>
        axiomsBuffer.addOne(Main.await(Axioms.compute(name, term))) // TODO: avoid await
      case Proofterm.PBound(index) =>
      case Proofterm.OfClass(typ, clazz) => ???
      case Proofterm.Oracle(name, term, typ) => ???
      case pthm@PThm(header, body) =>
        val thm = Main.await(Theorems.compute(pthm)) // TODO: avoid await
        axiomsBuffer.addAll(thm.axioms)

    findAxioms(proof)

    Future.successful(axiomsBuffer.result())
  }

}