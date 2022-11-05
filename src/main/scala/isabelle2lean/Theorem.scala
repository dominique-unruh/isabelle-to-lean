package isabelle2lean

import scala.language.implicitConversions
import de.unruh.isabelle.pure.Proofterm.PThm

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.pure.{Proofterm, Term, Typ}
import isabelle2lean.Theorem.{Serial, lookups}
import scalaz.{Cord, Show}

import scala.collection.mutable.ListBuffer
import scala.concurrent.Future
import scalaz.syntax.all.given
import OutputTerm.given
import OutputTerm.showOutputTerm
import scalaz.Scalaz.longInstance
import Utils.{zipStrict, given}

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

//noinspection UnstableApiUsage
case class Theorem(fullName: String, name: String, serial: Serial, axioms: List[Axiom#Instantiated],
                   typParams : List[TypeVariable]) {
  override def toString: String = s"Theorem(${name}@${serial})"

  inline def atIdentifier: Identifier = Identifier(fullName, at = true)

  override def equals(obj: Any): Boolean = ???

  override def hashCode(): Int = ???

  class Instantiated(val typs: List[ITyp], val axioms: List[Axiom#Instantiated]) {
    inline def theorem: Theorem.this.type = Theorem.this
    override def equals(obj: Any): Boolean = ???
    override def hashCode(): Int = ???
  }

  private val cache = new ConcurrentHashMap[List[ITyp], Future[Instantiated]]()

  def instantiate(typs: List[ITyp]): Future[Instantiated] = {
    lookups.incrementAndGet()
    cache.computeIfAbsent(typs, { _ =>
      Theorem.misses.incrementAndGet()
      val subst = typParams.zipStrict(typs)
      for (axioms <- Future.sequence (this.axioms.map (_.substitute (subst) ) ) )
        yield
          new Instantiated (typs = typs, axioms = axioms)
    })}

  def instantiate(pthm: PThm): Future[Instantiated] = {
    val typs = pthm.header.types.getOrElse(throw RuntimeException(s"No type instantiation provided in theorem $pthm"))
      .map(ITyp.apply)
    instantiate(typs)
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

    // TODO: Do we need the fully reconstructed proof?
    val proof: Proofterm = pthm.fullProof(ctxt.theoryOf)
    if (Globals.tryToParallelize)
      Future { triggerAllTheorems(proof) }

    val constantsBuffer = UniqueListBuffer[Constant#Instantiated]()
    val propString = Utils.translateTermClean(prop, constants = constantsBuffer)
//    val propConstants = constantsBuffer.toList

    for (typParams <- Utils.typParametersOfProp(prop);
         valParams <- Utils.valParametersOfProp(prop);
         axioms <- allAxiomsInProof(proof))
    yield {
      for (axiom <- axioms)
        constantsBuffer.addAll(axiom.constants.filterNot(_.isDefined))
      val constants = constantsBuffer.result()

      output.synchronized {
        output.println(cord"/-- Isabelle lemma $name (${pthm.header.serial}): ${prop.pretty(ctxt)} -/")
        output.println(cord"theorem $fullName")
        if (typParams.nonEmpty) {
          val typArgString : Cord = Utils.parenList(typParams.map(_.outputTerm), parens="{}")
          output.println(cord"     /- Type params -/  $typArgString")
        }
        if (constants.nonEmpty)
          val constsString = Utils.parenList(constants.map(_.asParameterTerm), sep = "\n                         ")
          output.println(cord"     /- Constants -/    $constsString")
        if (axioms.nonEmpty)
          val axiomsString = Utils.parenList(axioms.map(_.asParameterTerm), sep = "\n                         ")
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
      Theorem(fullName = fullName, name = name, serial = pthm.header.serial, axioms = axioms, typParams = typParams)
    }
  }


  /** Triggers computation of all invoked theorems to increase parallelism. */
  def triggerAllTheorems(proof: Proofterm): Unit = proof match
    case _: Proofterm.MinProof.type =>
    case Proofterm.AppP(proof1, proof2) => triggerAllTheorems(proof1); triggerAllTheorems(proof2)
    case Proofterm.Appt(proof, term) => triggerAllTheorems(proof)
    case Proofterm.AbsP(name, term, proof) => triggerAllTheorems(proof)
    case Proofterm.Abst(name, typ, proof) => triggerAllTheorems(proof)
    case _: Proofterm.Hyp =>
    case _: Proofterm.PAxm =>
    case _: Proofterm.PBound =>
    case _: Proofterm.OfClass =>
    case _: Proofterm.Oracle =>
    case pthm: PThm => Theorems.compute(pthm)

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
        val axiom = Axioms.get(name);
        assert(axiom.prop == term);
        assert(typs.nonEmpty);
        for (instantiated <- axiom.instantiate(typs.get.map(ITyp.apply)))
          yield
            if (!instantiated.isProven)
              axiomsBuffer.addOne(instantiated)
      case Proofterm.PBound(index) => Future.unit
      case Proofterm.OfClass(typ, clazz) => ???
      case Proofterm.Oracle(name, term, typ) => ???
      case pthm @ PThm(header, body) =>
        for (thm <- Theorems.compute(pthm);
             inst <- thm.instantiate(pthm))
          yield
            axiomsBuffer.addAll(inst.axioms.filterNot(_.isProven))
    for (_ <- findAxioms(proof))
      yield axiomsBuffer.result()
  }

  private val lookups = new AtomicInteger
  private val misses = new AtomicInteger

  def printStats(): Unit =
    println(s"Instantiated axiom stats: ${misses.get}/${lookups.get}")
}


/*

From first attempt:


//noinspection UnstableApiUsage
object Theorem {
  case class Env(propEnv: List[String] = Nil, termEnv: List[String] = Nil,
                 boundFree: Set[String] = Set.empty, boundVar: Set[(String, Int)] = Set.empty)

  /** Assumption: All names in AbsP are non-empty and no shadowing */
  def proofToString(proof: Proofterm, env: Env): Future[OutputTerm] = {
    def intersperseWildcards(terms: Seq[OutputTerm]): Seq[OutputTerm] = terms.flatMap(t => Seq(t, Wildcard))

    proof match {
      case Proofterm.MinProof =>
        throw new RuntimeException("MinProof")
      case Proofterm.AppP(proof1, proof2) =>
        val out1future = proofToString(proof1, env)
        val out2future = proofToString(proof2, env)
        for (out1 <- out1future;
             out2 <- out2future)
        yield Application(out1, out2)
      case Proofterm.Appt(proof, term) =>
        assert(term.nonEmpty)
        for (out <- proofToString(proof, env))
          yield Application(out,
            Main.translateTermClean(term.get, env = env.termEnv, defaultAllBut = Some((env.boundVar, env.boundFree))))
      case Proofterm.AbsP(name, term, proof) =>
        assert(term.nonEmpty)
        assert(name.nonEmpty)
        val name2 = Naming.mapName(name, category = Namespace.ProofAbsVar)
        for (out <- proofToString(proof, env.copy(propEnv = name2 :: env.propEnv)))
          yield Abstraction(name2,
            Main.translateTermClean(term.get, env = env.termEnv, defaultAllBut = Some((env.boundVar, env.boundFree))), out)
      case Proofterm.Abst(name, typ, proof) =>
        assert(typ.nonEmpty)
        assert(name.nonEmpty)
        val name2 = Naming.mapName(name, category = Namespace.ProofAbsVarTerm)
        for (out <- proofToString(proof, env.copy(termEnv = name2 :: env.termEnv)))
          yield Abstraction(name2, Main.translateTyp(typ.get), out)
      case Proofterm.Hyp(term) =>
        ???
      case Proofterm.PAxm(name, prop, typ) =>
        val axiom = Axioms.compute(name, prop)
        assert(typ.nonEmpty)
        Future.successful(Application(Identifier(axiom.fullName, at = true), intersperseWildcards(typ.get.map(Main.translateTyp)): _*))
      case Proofterm.PBound(index) =>
        Future.successful(Identifier(env.propEnv(index)))
      case Proofterm.OfClass(typ, clazz) =>
        ???
      case Proofterm.Oracle(name, term, typ) =>
        ???
      case pthm: PThm =>
        assert(pthm.header.types.nonEmpty)
        val types = pthm.header.types.get.map(Main.translateTyp)
        for (theorem <- Theorems.compute(pthm))
          yield Application(Identifier(theorem.fullName, at = true), intersperseWildcards(types): _*)
    }
  }
}

*/