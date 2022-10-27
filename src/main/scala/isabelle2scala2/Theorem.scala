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
      name = (name, pthm.header.serial),
      suggestion = if (name.nonEmpty) name else "thm_" + pthm.header.serial,
      category = Namespace.Theorem)

    val proof: Proofterm = pthm.fullProof(ctxt.theoryOf)
    val argString = Main.argumentsOfProp_OLD(prop)
    val propString = Main.translateTermClean(prop)

    Future {
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

      val axioms = axiomsBuffer.result()

      output.synchronized {
        output.println(s"-- Lemma ${name} (${pthm.header.serial}): ${prop.pretty(ctxt)}")
        output.println(s"-- Uses: ${axioms.map(_.name).mkString(" ")}")
        output.println()
        output.flush()
      }

//      println(s"Done: ${pthm.header.name}")
      Theorem(name = name, serial = pthm.header.serial, axioms = axiomsBuffer.toList)
    }
  }
}
