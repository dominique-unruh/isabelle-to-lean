package isabelle2scala

import de.unruh.isabelle.pure.Proofterm.{AbsP, Abst, AppP, Appt, PThm}

import java.io.PrintWriter
import Globals.ctxt
import Globals.given
import de.unruh.isabelle.pure.{Proofterm, Term}
import org.apache.commons.io.filefilter.TrueFileFilter
import org.apache.commons.text.WordUtils
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import isabelle2scala.Theorem.{Env, proofToString}
import org.checkerframework.dataflow.qual.Pure

import scala.concurrent.{Await, blocking}
import scala.concurrent.duration.Duration

//noinspection UnstableApiUsage
case class Theorem(pthm: PThm) extends LogicalEntity {
  override def toString: String = s"Theorem(${pthm.header.name}@${pthm.header.serial})"

  val fullName: String = Naming.mapName(
    name = (name, pthm.header.serial),
    suggestion = if (name.nonEmpty) name else "thm_" + pthm.header.serial,
    category = Namespace.Theorem)

  def proof: Proofterm = pthm.fullProof(ctxt.theoryOf)

  def print(output: PrintWriter): Unit = {
    val argString = Main.argumentsOfProp(prop)
    val propString = Main.translateTermClean(prop)
    val proof = this.proof

    // TODO: this is duplication, argumentsOfProp already scans for vars/frees
    val vars = IsabelleOps.addVars(prop).retrieveNow.reverse.map(_._1)
    val frees = IsabelleOps.addFrees(prop).retrieveNow.reverse.map(_._1)
    val env = Env(boundFree = frees.toSet, boundVar = vars.toSet)

    val proofString = proofToString(cleanDuplicateAbsNamesProof(proof), env)

    output.synchronized {
      output.println(s"-- Lemma ${name} (${pthm.header.serial}): ${prop.pretty(ctxt)}")
      output.println(s"theorem $fullName $argString: $propString")
      val wrappedProofString = WordUtils.wrap(proofString.toString, 150, "\n     ", false)
      output.println(s"  := $wrappedProofString")
      output.println()
      output.flush()
    }
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
}

//noinspection UnstableApiUsage
object Theorem {
  case class Env(propEnv: List[String] = Nil, termEnv: List[String] = Nil,
                 boundFree: Set[String] = Set.empty, boundVar: Set[(String, Int)] = Set.empty)

  /** Assumption: All names in AbsP are non-empty and no shadowing */
  // TODO: Use futures
  def proofToString(proof: Proofterm, env: Env): OutputTerm = {
    def intersperseWildcards(terms: Seq[OutputTerm]): Seq[OutputTerm] = terms.flatMap(t => Seq(t, Wildcard))

    proof match {
      case Proofterm.MinProof =>
        throw new RuntimeException("MinProof")
      case Proofterm.AppP(proof1, proof2) =>
        Application(proofToString(proof1, env), proofToString(proof2, env))
      case Proofterm.Appt(proof, term) =>
        assert(term.nonEmpty)
        Application(proofToString(proof, env),
          Main.translateTermClean(term.get, env = env.termEnv, defaultAllBut = Some((env.boundVar, env.boundFree))))
      case Proofterm.AbsP(name, term, proof) =>
        assert(term.nonEmpty)
        assert(name.nonEmpty)
        val name2 = Naming.mapName(name, category = Namespace.ProofAbsVar)
        Abstraction(name2,
          Main.translateTermClean(term.get, env = env.termEnv, defaultAllBut = Some((env.boundVar, env.boundFree))),
          proofToString(proof, env.copy(propEnv = name2 :: env.propEnv)))
      case Proofterm.Abst(name, typ, proof) =>
        assert(typ.nonEmpty)
        assert(name.nonEmpty)
        val name2 = Naming.mapName(name, category = Namespace.ProofAbsVarTerm)
        Abstraction(name2, Main.translateTyp(typ.get), proofToString(proof, env.copy(termEnv = name2 :: env.termEnv)))
      case Proofterm.Hyp(term) =>
        ???
      case Proofterm.PAxm(name, prop, typ) =>
        val axiom = Axioms.compute(name, prop)
        assert(typ.nonEmpty)
        Application(Identifier(axiom.fullName, at = true), intersperseWildcards(typ.get.map(Main.translateTyp)): _*)
      case Proofterm.PBound(index) =>
        Identifier(env.propEnv(index))
      case Proofterm.OfClass(typ, clazz) =>
        ???
      case Proofterm.Oracle(name, term, typ) =>
        ???
      case pthm: PThm =>
        val theorem = blocking { Await.result(Theorems.compute(pthm), Duration.Inf) }
        assert(pthm.header.types.nonEmpty)
        val types = pthm.header.types.get.map(Main.translateTyp)
        Application(Identifier(theorem.fullName, at = true), intersperseWildcards(types): _*)
    }
  }
}