package isabelle2scala2

import de.unruh.isabelle.pure.{ConcreteTerm, Term, Typ}

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import Utils.zipStrict

import scala.concurrent.Future

case class Axiom private[Axiom] (fullName: String, name: String, prop: ConcreteTerm,
                                 constants: List[Constant#Instantiated], typParams: List[TypeVariable]) {
  override def toString: String = s"Axiom($name)"

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

  inline def identifier: Identifier = Identifier(fullName)

  case class Instantiated(fullName: String, typArgs: List[Typ], constants: List[Constant#Instantiated]) {
    inline def axiom: Axiom = Axiom.this

    /** Returns "instantiated-fullName : axiom-fullName typArgs" */
    def outputTerm: OutputTerm =
      TypeConstraint(identifier,
        Application(
          Application(axiom.identifier, typArgs.map(Utils.translateTyp) :_*),
          constants.map(_.identifier) :_*))

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

      val constsString = constants map { c => Parentheses(c.outputTerm) } mkString " "

      output.synchronized {
        output.println(s"/-- Def of Isabelle axiom $name: ${prop.pretty(ctxt)} -/")
        output.println(s"def $fullName")
        if (typParams.nonEmpty)
          output.println(s"     /- Type args -/  $typParams")
        if (constsString.nonEmpty)
          output.println(s"     /- Constants -/  $constsString")
        if (valParams.nonEmpty)
          output.println(s"     /- Value args -/ $valParams")
        output.println(s"  := $propString")
        output.println()
        output.flush()
      }
      Axiom(fullName = fullName, typParams = typParams, name = name, prop = prop, constants = constants)
    }
  }
}