package isabelle2scala

import de.unruh.isabelle.pure.Proofterm.{AbsP, Abst, AppP, Appt, PThm}

import java.io.PrintWriter
import Globals.ctxt
import Globals.given
import de.unruh.isabelle.pure.{Proofterm, Term}
import org.apache.commons.io.filefilter.TrueFileFilter

import scala.concurrent.ExecutionContext.Implicits.given

//noinspection UnstableApiUsage
case class Theorem(pthm: PThm) extends LogicalEntity {
  override def toString: String = s"Theorem(${pthm.header.name}@${pthm.header.serial})"

  val fullName: String = Naming.mapName(name = s"${name}@${pthm.header.serial}", category = Namespace.Theorem)

  def proof: Proofterm = pthm.fullProof(ctxt.theoryOf)

  def print(output: PrintWriter): Unit = {
    println(s"YYY: ${name}: ${prop.pretty(ctxt)}")
    val argString = Main.argumentsOfProp(prop)
    val propString = Main.translateTermClean(prop)
    val proof = this.proof
    val proofString = proofToString(cleanDuplicateAbsNamesProof(proof), Nil, Nil)

    output.println(s"-- Lemma ${name} (${pthm.header.serial}): ${prop.pretty(ctxt)}")
    output.println(s"-- Proof: $proof")
    output.println(s"theorem $fullName $argString: $propString")
    output.println(s"  := $proofString")
    output.println()
    output.flush()

    output.println(s"-- Proof: $proofString")
    output.println()
    output.flush()
  }

  def cleanDuplicateAbsNamesProof(proof: Proofterm, used: Set[String] = Set.empty): Proofterm = {
    def getUnused(name: String): String = {
      var name2 = if (name.isEmpty) "x" else name
      while (used.contains(name2))
        name2 += '\''
      name2
    }

    proof match {
      case AppP(t, u) =>
        val tClean = cleanDuplicateAbsNamesProof(t, used)
        val uClean = cleanDuplicateAbsNamesProof(u, used)
        if ((tClean eq t) && (uClean eq u))
          proof
        else
          AppP(tClean, uClean)
      case Appt(t, u) =>
        val tClean = cleanDuplicateAbsNamesProof(t, used)
        if (tClean eq t)
          proof
        else
          Appt(tClean, u)
      case AbsP(x, typ, body) =>
        val x2 = getUnused(x)
        val bodyClean = cleanDuplicateAbsNamesProof(body, used + x2)
        if ((x2 eq x) && (bodyClean eq body))
          proof
        else
          AbsP(x2, typ, bodyClean)

      case Abst(x, typ, body) =>
        val x2 = getUnused(x)
        val bodyClean = cleanDuplicateAbsNamesProof(body, used + x2)
        if ((x2 eq x) && (bodyClean eq body))
          proof
        else
          Abst(x2, typ, bodyClean)

      case Proofterm.MinProof | Proofterm.Hyp(_) | Proofterm.PAxm(_, _, _) | Proofterm.PBound(_) |
           Proofterm.OfClass(_, _) | Proofterm.Oracle(_, _, _) | PThm(_, _) => proof
    }
  }

  def prop: Term = pthm.header.prop

  def name: String = pthm.header.name

  /** Assumption: All names in AbsP are non-empty and no shadowing */
  def proofToString(proof: Proofterm, propEnv: List[String] = Nil, termEnv: List[String]): OutputTerm = {
    proof match {
      case Proofterm.MinProof =>
        throw new RuntimeException("MinProof")
      case Proofterm.AppP(proof1, proof2) =>
        Application(proofToString(proof1, propEnv, termEnv), proofToString(proof2, propEnv, termEnv))
      case Proofterm.Appt(proof, term) =>
        assert(term.nonEmpty)
        Application(proofToString(proof, propEnv, termEnv), Main.translateTermClean(term.get, env = termEnv))
      case Proofterm.AbsP(name, term, proof) =>
        assert(term.nonEmpty)
        assert(name.nonEmpty)
        val name2 = Naming.mapName(name, category = Namespace.ProofAbsVar)
        Abstraction(name2, Main.translateTermClean(term.get, env = termEnv), proofToString(proof, name2 :: propEnv, termEnv))
      case Proofterm.Abst(name, typ, proof) =>
        assert(typ.nonEmpty)
        assert(name.nonEmpty)
        val name2 = Naming.mapName(name, category = Namespace.ProofAbsVarTerm)
        Abstraction(name2, Main.translateTyp(typ.get), proofToString(proof, propEnv, name2 :: termEnv))
      case Proofterm.Hyp(term) =>
        ???
      case Proofterm.PAxm(name, prop, typ) =>
        val axiom = Axioms.compute(name, prop)
        assert(typ.nonEmpty)
        Application(Identifier(axiom.fullName, at = true), typ.get.map(Main.translateTyp) :_*)
      case Proofterm.PBound(index) =>
        Identifier(propEnv(index))
      case Proofterm.OfClass(typ, clazz) =>
        ???
      case Proofterm.Oracle(name, term, typ) =>
        ???
      case pthm: PThm =>
        val theorem = Theorems.compute(pthm)
        println(s"XXX ${theorem.name}, ${theorem.prop.pretty(ctxt)}, ${pthm.header.types.get.map(_.pretty(ctxt))}")
        assert(pthm.header.types.nonEmpty)
        val types = pthm.header.types.get.map(Main.translateTyp)
        Comment(s"${pthm.header.types.get.map(_.pretty(ctxt))}", Application(Identifier(theorem.fullName, at = true), types :_*))
    }
  }
}
