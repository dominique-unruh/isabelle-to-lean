package isabelle2lean

import scala.language.implicitConversions

import de.unruh.isabelle.pure.{ConcreteTerm, Term, Typ}

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import Utils.{mkCord, zipStrict, toCord, given}

import scala.concurrent.Future
import OutputTerm.showOutputTerm
import scalaz.Cord
import scalaz.syntax.show.cordInterpolator

case class Axiom private[Axiom] (fullName: String, name: String, prop: ConcreteTerm,
                                 constants: List[Constant#Instantiated], typParams: List[TypeVariable]) {
  override def toString: String = s"Axiom($name)"

  def shortSummary: Cord = cord"$name: ${prop.pretty(ctxt)}"

  override def hashCode(): Int = name.hashCode

  override def equals(obj: Any): Boolean = obj match {
    case axiom: Axiom => name == axiom.name
    case _ => false
  }

  def instantiate(typArgs: List[Typ]): Future[Instantiated] = {
    val fullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.AxiomInstantiated)
    val constants2 = constants.map(_.substitute(typParams.zipStrict(typArgs)))
    for (constants3 <- Future.sequence(constants2))
      yield
        Instantiated(fullName = fullName, typArgs = typArgs, constants = constants3)
  }

  inline def atIdentifier: Identifier = Identifier(fullName, at = true)

  case class Instantiated(fullName: String, typArgs: List[Typ], constants: List[Constant#Instantiated]) {
    inline def axiom: Axiom = Axiom.this

    def shortSummary: Cord = {
      val summary1 = cord"$name: \"${prop.pretty(ctxt)}\""
      if (typArgs.isEmpty)
        summary1
      else
        cord"$summary1 for ${typArgs.map(_.pretty(ctxt).toCord).mkCord(", ")}"
    }

    /** Returns "instantiated-fullName : axiom-fullName typArgs" */
    def outputTerm: OutputTerm =
      Comment(shortSummary.shows,
        TypeConstraint(identifier,
          Application(
            Application(axiom.atIdentifier, typArgs.map(Utils.translateTyp) :_*),
            constants.map(_.identifier) :_*)))

    inline def identifier: Identifier = Identifier(fullName)

    def substitute(subst: IterableOnce[(TypeVariable, Typ)]): Future[Instantiated] =
      for (typArgs2 <- Utils.substituteTypArgs(typArgs, subst);
           inst <- Axiom.this.instantiate(typArgs2))
        yield inst

    override def hashCode(): Int = fullName.hashCode

    override def equals(obj: Any): Boolean = obj match
      case inst: Instantiated => fullName == inst.fullName
      case _ => false
  }
}

object Axiom {
  def createAxiom(name: String, prop: ConcreteTerm, output: PrintWriter): Future[Axiom] = {
    val fullName: String = Naming.mapName(prefix = "axiom_", name = name, category = Namespace.Axiom)
    for (typParams <- Utils.typParametersOfProp(prop);
         valParams <- Utils.valParametersOfProp(prop)) yield {

      val constantsBuffer = UniqueListBuffer[Constant#Instantiated]()
      val propString = Utils.translateTermClean(prop, constants = constantsBuffer)
      val constants = constantsBuffer.result()


      output.synchronized {
        output.println(s"/-- Def of Isabelle axiom $name: ${prop.pretty(ctxt)} -/")
        output.println(s"def $fullName")
        if (typParams.nonEmpty)
          val typParamsString = typParams map { p => Parentheses(p.identifier) } mkCord " "
          output.println(cord"     /- Type params -/   $typParamsString")
        if (constants.nonEmpty)
          val constsString = constants map { c => Parentheses(c.outputTerm) } mkCord " "
          output.println(cord"     /- Constants -/     $constsString")
        output.print("  := ")
        if (valParams.nonEmpty)
          val valParamsString = valParams map { c => Parentheses(c.outputTerm) } mkCord " "
          output.print(cord"/- Value params -/  forall $valParamsString,\n    ")
        output.println(propString)
        output.println()
        output.flush()
      }
      Axiom(fullName = fullName, typParams = typParams, name = name, prop = prop, constants = constants)
    }
  }
}
