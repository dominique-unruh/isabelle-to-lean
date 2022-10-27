package isabelle2scala2

import de.unruh.isabelle.pure.{ConcreteTerm, Term}

import java.io.PrintWriter
import Globals.{ctxt, given}

import scala.concurrent.Future

case class Axiom private[Axiom] (fullName: String, name: String, prop: ConcreteTerm, constants: List[Constant#Instantiated]) {
  override def toString: String = s"Axiom($name)"

  override def hashCode(): Int = name.hashCode

  override def equals(obj: Any): Boolean = obj match {
    case axiom: Axiom => name == axiom.name
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

      val constsString = constants map { const =>
        val args = const.typArgs map { typ => s" (${Utils.translateTyp(typ)})" } mkString " "
        s"(${const.fullName}: ${const.constant.fullName}$args)"
      } mkString(" ")

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