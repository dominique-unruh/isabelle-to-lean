package isabelle2lean

import scala.language.implicitConversions
import de.unruh.isabelle.pure.{ConcreteTerm, Term, Typ}

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import Utils.{mkCord, toCord, valParametersOfProp, zipStrict, given}

import scala.concurrent.{Await, Future}
import OutputTerm.showOutputTerm
import isabelle2lean.Axiom.{lookups, misses}
import scalaz.Cord
import scalaz.syntax.show.cordInterpolator

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import scala.concurrent.duration.Duration

case class Axiom private[Axiom] (fullName: String, name: String,
                                 // TODO: This is actually not really needed. Remove for efficiency (or just MLValue-ref)
                                 prop: ConcreteTerm,
                                 constants: List[Constant#Instantiated], typParams: List[TypeVariable],
                                 proofs: List[Axiom.Proof]) {
  override def toString: String = s"Axiom($name)"

  def shortSummary: Cord = cord"$name: ${prop.pretty(ctxt)}"

  override def hashCode(): Int = name.hashCode

  override def equals(obj: Any): Boolean = obj match {
    case axiom: Axiom => name == axiom.name
    case _ => false
  }

  private val cache = new ConcurrentHashMap[List[ITyp], Future[Instantiated]]()

  def instantiate(typArgs: List[ITyp]): Future[Instantiated] = {
    lookups.incrementAndGet()
    cache.computeIfAbsent(typArgs, { _ =>
      misses.incrementAndGet()
      val fullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.AxiomInstantiated)
      val constants2 = constants.map(_.substitute(typParams.zipStrict(typArgs)))
      for (constants3 <- Future.sequence(constants2))
        yield
          Instantiated(fullName = fullName, typArgs = typArgs, constants = constants3) })
  }

  inline def atIdentifier: Identifier = Identifier(fullName, at = true)

  case class Instantiated(fullName: String, typArgs: List[ITyp], constants: List[Constant#Instantiated]) {
    inline def axiom: Axiom = Axiom.this

    def shortSummary: Cord = {
      val summary1 = cord"$name: \"${prop.pretty(ctxt)}\""
      if (typArgs.isEmpty)
        summary1
      else
        cord"$summary1 for ${typArgs.map(_.pretty.toCord).mkCord(", ")}"
    }

    /** Returns "instantiated-fullName : axiom-fullName typArgs" */
    def asParameterTerm: OutputTerm = {
      assert(!isProven)
      Comment(shortSummary.shows,
        TypeConstraint(identifier,
          Application(
            Application(axiom.atIdentifier, typArgs.map(_.outputTerm): _*),
            constants.map(_.asUsageTerm): _*)))
    }

    inline def identifier: Identifier = {
      assert(!isProven)
      Identifier(fullName)
    }

    def substitute(subst: IterableOnce[(TypeVariable, ITyp)]): Future[Instantiated] =
      for (typArgs2 <- Utils.substituteTypArgs(typArgs, subst);
           inst <- Axiom.this.instantiate(typArgs2))
      yield inst

    override def hashCode(): Int = fullName.hashCode

    override def equals(obj: Any): Boolean = obj match
      case inst: Instantiated => fullName == inst.fullName
      case _ => false

    lazy val proofMatch: Option[OutputTerm] = {
      val matches = proofs.map(_.matches(typArgs)) // List of futures of optional results
      val matches2 = Await.result(Future.sequence(matches), Duration.Inf)
      val matches3 = matches2.flatten // List of results
      matches3 match {
        case List() => None
        case List(m) =>
          println(s"AXIOM MATCH: ${Axiom.this.name} @ ${typArgs.map(_.pretty.toCord).mkCord(" ")} -> $m")
          Some(m)
        case _ =>
          throw new AssertionError(s"Colliding definitions for $name: $matches")
      }
    }

    def isProven: Boolean = proofMatch.nonEmpty
  }
}

object Axiom {
  /** A proof of the axiom, possibly at a smaller type */
  case class Proof(name: String,
                   /** Type arguments with which the Axiom type is instantiated */
                   typArgs: List[ITyp],
                   body: Cord,
                   /** Type parameters this axiom's proof has */
                   typParams: List[TypeVariable] = Nil) {
    val fullName: String = Naming.mapName(name = name, extra = typArgs, category = Namespace.AxiomProof)

    def matches(specificTypArgs: List[ITyp]): Future[Option[OutputTerm]] =
      for (m <- IsabelleOps.typListMatch(Globals.thy, typArgs.map(_.typ).zipStrict(specificTypArgs.map(_.typ))).retrieve)
        yield
          m match
            case None => None
            case Some(matchTyps) =>
              val matchTypMap = Map.from( matchTyps.map { case (name,index,typ) => TypeVariable.tvar(name,index) -> ITyp(typ) } )
              val typArgs = typParams.map(matchTypMap)
              Some(Application(atIdentifier, typArgs.map(_.outputTerm) :_*))

    def atIdentifier: Identifier = Identifier(fullName, at = true)
  }

  def createAxiom(name: String, prop: ConcreteTerm, output: PrintWriter,
                  proofs: List[Proof]): Future[Axiom] = {
    val axiomFullName: String = Naming.mapName(prefix = "axiom_", name = name, category = Namespace.Axiom)
    for (typParams <- Utils.typParametersOfProp(prop);
         valParams <- Utils.valParametersOfProp(prop)) yield {

      val constantsBuffer = UniqueListBuffer[Constant#Instantiated]()
      val propString = Utils.translateTermClean(prop, constants = constantsBuffer)
      val constants = constantsBuffer.result()

      output.synchronized {
        output.println(s"/-- Def of Isabelle axiom $name: ${prop.pretty(ctxt)} -/")
        output.println(s"noncomputable def $axiomFullName")
        if (typParams.nonEmpty)
          val typParamsString = Utils.parenList(typParams.map(_.outputTerm))
          output.println(cord"     /- Type params -/   $typParamsString")
        if (constants.nonEmpty)
          val constsString = Utils.parenList(constants.map(_.asParameterTerm), sep = "\n                         ")
          output.println(cord"     /- Constants -/     $constsString")
        output.print("  := ")
        if (valParams.nonEmpty)
          val valParamsString = Utils.parenList(valParams.map(_.outputTerm))
          output.print(cord"/- Value params -/  forall $valParamsString,\n     ")
        output.println(propString)
        output.println()
        for (proof <- proofs) {
          val proofValParams = valParams.map(_.substitute(TypSubstitution(typParams, proof.typArgs)))
          // TODO: Needs to abstract over the free type variables
          val proofTypParamString = Utils.parenList(proof.typParams.map(_.outputTerm), prefix = " ")
          val proofValParamString = Utils.parenList(proofValParams.map(_.outputTerm), prefix = " ")
          val proofProp = IsabelleOps.substituteTypsInTerm(typParams.map(_.typ).zipStrict(proof.typArgs.map(_.typ)), prop).retrieveNow
          val proofPropOutputTerm = Utils.translateTermClean(proofProp, constants = ForgetfulBuffer(constant => assert(constant.isDefined)))
          output.println(cord"/-- Proof of Isabelle axiom $name ${prop.pretty(ctxt)}, for typ args ${proof.typArgs.mkCord(", ")} -/")
          output.println(cord"noncomputable def ${proof.fullName}$proofTypParamString$proofValParamString : ${proofPropOutputTerm}")
          output.println(cord"  := ${proof.body}")
          output.println()
        }
        output.flush()
      }

      Axiom(fullName = axiomFullName, typParams = typParams, name = name, prop = prop, constants = constants,
        proofs = proofs)
    }
  }

  private val lookups = new AtomicInteger
  private val misses = new AtomicInteger

  def printStats(): Unit =
    println(s"Instantiated axiom stats: ${misses.get}/${lookups.get}")
}
