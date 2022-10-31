package isabelle2scala2

import de.unruh.isabelle.pure.{ConcreteTerm, Term, Typ}

import java.io.PrintWriter
import Globals.{ctxt, given}
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given

import scala.concurrent.{Future}

case class Axiom private[Axiom] (fullName: String, name: String, prop: ConcreteTerm, constants: List[Constant#Instantiated]) {
  override def toString: String = s"Axiom($name)"

  override def hashCode(): Int = name.hashCode

  override def equals(obj: Any): Boolean = obj match {
    case axiom: Axiom => name == axiom.name
    case _ => false
  }

  def instantiate(typArgs: List[Typ]): Instantiated = {
    val fullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.AxiomInstantiated)
    Instantiated(fullName = fullName, typArgs = typArgs)
  }

  case class Instantiated(fullName: String, typArgs: List[Typ]) {
    inline def axiom: Axiom = Axiom.this

    /** Returns "instantiated-fullName : axiom-fullName typArgs"
     * TODO: should add constants */
    def outputTerm: OutputTerm =
      TypeConstraint(Identifier(fullName), Application(Identifier(axiom.fullName), typArgs.map(Utils.translateTyp) :_*))

    def substitute(subst: IterableOnce[(TypeVariable, Typ)]): Future[Instantiated] = {
      val subst2 : List[(Typ,Typ)] = subst.iterator.map{case (t,u) => (t.typ, u)}.toList
      val typArgs2 = typArgs.map(IsabelleOps.substituteTyp(subst2, _).retrieve)
      for (typArgs3 <- Future.sequence(typArgs2))
        yield {
          val newFullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.AxiomInstantiated)
          Instantiated(fullName = newFullName, typArgs = typArgs3)
        }
    }

    override def hashCode(): Int = fullName.hashCode

    override def equals(obj: Any): Boolean = obj match
      case inst: Instantiated => fullName == inst.fullName
      case _ => false
  }
}

object Axiom {
  def createAxiom(name: String, prop: ConcreteTerm, output: PrintWriter): Future[Axiom] = {
    val fullName: String = Naming.mapName(prefix = "axiom_", name = name, category = Namespace.Axiom)
    for (typArgs <- Utils.typArgumentsOfProp(prop);
         valArgs <- Utils.valArgumentsOfProp(prop)) yield {

      val constantsBuffer = UniqueListBuffer[Constant#Instantiated]()
      val propString = Utils.translateTermClean(prop, constants = constantsBuffer)
      val constants = constantsBuffer.result()

      val constsString = constants map { c => Parentheses(c.outputTerm) } mkString " "

      output.synchronized {
        output.println(s"/-- Def of Isabelle axiom $name: ${prop.pretty(ctxt)} -/")
        output.println(s"def $fullName")
        if (typArgs.nonEmpty)
          output.println(s"     /- Type args -/  $typArgs")
        if (constsString.nonEmpty)
          output.println(s"     /- Constants -/  $constsString")
        if (valArgs.nonEmpty)
          output.println(s"     /- Value args -/ $valArgs")
        output.println(s"  := $propString")
        output.println()
        output.flush()
      }
      Axiom(fullName = fullName, name = name, prop = prop, constants = constants)
    }
  }
}