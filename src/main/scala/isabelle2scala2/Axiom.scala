package isabelle2scala2

import de.unruh.isabelle.pure.Term

import java.io.PrintWriter
import Globals.{ctxt, given}

import scala.concurrent.Future

case class Axiom private[Axiom] (fullName: String, name: String, prop: Term) {
  override def toString: String = s"Axiom($name)"

  override def hashCode(): Int = name.hashCode

  override def equals(obj: Any): Boolean = obj match {
    case axiom: Axiom => name == axiom.name
    case _ => false
  }
}

object Axiom {
  def createAxiom(name: String, prop: Term, output: PrintWriter) : Future[Axiom] = Future {
    val fullName: String = Naming.mapName(prefix = "axiom_", name = name, category = Namespace.Axiom)
    val argString = Main.argumentsOfProp(prop)
    val propString = Main.translateTermClean(prop)
    // TODO consts
    val constsString = "...consts..."
    output.synchronized {
      output.println(s"-- Axiom $name: ${prop.pretty(ctxt)}")
      output.println(s"def $fullName")
      output.println(s"      $argString -- type args")
      output.println(s"      -- $constsString -- constants")
      output.println(s"  = $propString")
      output.println()
      output.flush()
    }
    Axiom(fullName = fullName, name = name, prop = prop)
  }
}
