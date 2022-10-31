package isabelle2scala2

import scala.language.implicitConversions

import de.unruh.isabelle.pure.Proofterm.PThm

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.pure.{Proofterm, Term, Typ}
import isabelle2scala2.Theorem.Serial
import scalaz.{Cord, Show}

import scala.collection.mutable.ListBuffer
import scala.concurrent.Future
import scalaz.syntax.all.given
import OutputTerm.given
import OutputTerm.showOutputTerm
import scalaz.Scalaz.longInstance
import Utils.{zipStrict, given}

//noinspection UnstableApiUsage
case class Theorem(fullName: String, name: String, serial: Serial, axioms: List[Axiom#Instantiated],
                   typArgs : List[TypeVariable]) {
  override def toString: String = s"Theorem(${name}@${serial})"

  inline def atIdentifier: Identifier = Identifier(fullName, at = true)

  class Instantiated(val typs: List[Typ], val axioms: List[Axiom#Instantiated]) {
    inline def theorem: Theorem.this.type = Theorem.this
    override def equals(obj: Any): Boolean = ???
    override def hashCode(): Int = ???
  }

  def instantiate(pthm: PThm): Future[Instantiated] = {
    val typs = pthm.header.types.getOrElse(throw RuntimeException(s"No type instantiation provided in theorem $pthm"))
    val typargs = this.typArgs
    val subst = typargs.zipStrict(typs)
    for (axioms <- Future.sequence( this.axioms.map(_.substitute(subst))) )
      yield
        new Instantiated(typs = typs, axioms = axioms)
  }
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

    for (typParams <- Utils.typParametersOfProp(prop);
         valParams <- Utils.valParametersOfProp(prop);
         axioms <- allAxiomsInProof(proof))
    yield {
      for (axiom <- axioms)
        constantsBuffer.addAll(axiom.constants)
      val constants = constantsBuffer.result()

      output.synchronized {
        output.println(cord"/-- Isabelle lemma $name (${pthm.header.serial}): ${prop.pretty(ctxt)} -/")
        output.println(cord"theorem $fullName")
        if (typParams.nonEmpty) {
          val typArgString : Cord = Utils.parenList(typParams.map(_.outputTerm), parens="{}")
          output.println(cord"     /- Type params -/  $typArgString")
        }
        if (constants.nonEmpty)
          val constsString = Utils.parenList(constants.map(_.outputTerm))
          output.println(cord"     /- Constants -/    $constsString")
        if (axioms.nonEmpty)
          val axiomsString = Utils.parenList(axioms.map(_.outputTerm), sep = "\n                        ")
          output.println(cord"     /- Axioms -/       $axiomsString")
        if (valParams.nonEmpty)
          val valParamString : Cord = Utils.parenList(valParams.map(_.outputTerm))
          output.println(cord"     /- Value params -/ $valParamString")
        output.println(cord"  : $propString :=")
        output.println()
        output.println(cord"  proof_omitted")
        output.println()
        output.flush()
      }

//      println(s"Done: ${pthm.header.name}")
      Theorem(fullName = fullName, name = name, serial = pthm.header.serial, axioms = axioms, typArgs = typParams)
    }
  }

  def allAxiomsInProof(proof: Proofterm): Future[List[Axiom#Instantiated]] = {
    val axiomsBuffer = new UniqueListBuffer[Axiom#Instantiated]

    // Don't parallelize because UniqueListBuffer is not thread safe
    def findAxioms(prf: Proofterm): Future[Unit] = prf match
      case Proofterm.MinProof => ???
      case Proofterm.AppP(proof1, proof2) =>
        for (_ <- findAxioms(proof1);
             _ <- findAxioms(proof2))
        yield {}
      case Proofterm.Appt(proof, term) => findAxioms(proof)
      case Proofterm.AbsP(name, term, proof) => findAxioms(proof)
      case Proofterm.Abst(name, typ, proof) => findAxioms(proof)
      case Proofterm.Hyp(term) => Future.unit
      case Proofterm.PAxm(name, term, typs) =>
        for (axiom <- Axioms.compute(name, term);
             _ = assert(typs.nonEmpty);
             instantiated <- axiom.instantiate(typs.get))
          yield
            axiomsBuffer.addOne(instantiated)
      case Proofterm.PBound(index) => Future.unit
      case Proofterm.OfClass(typ, clazz) => ???
      case Proofterm.Oracle(name, term, typ) => ???
      case pthm@PThm(header, body) =>
        for (thm <- Theorems.compute(pthm);
             inst <- thm.instantiate(pthm))
          yield
            axiomsBuffer.addAll(inst.axioms)
    for (_ <- findAxioms(proof))
      yield axiomsBuffer.result()
  }
}