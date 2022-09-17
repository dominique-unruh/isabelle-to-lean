package isabelle2scala

import de.unruh.isabelle.pure.Term

import java.io.PrintWriter
import Globals.ctxt

import concurrent.ExecutionContext.Implicits.given
import Globals.given

case class Axiom(name: String, prop: Term) extends LogicalEntity {
  override def toString: String = s"Axiom($name)"

  val fullName: String = Naming.quote(prefix = "axiom_", name = name, category = Namespace.Axiom)

  def print(output: PrintWriter): Unit = {
    val argString = Main.argumentsOfProp(prop)
    // TODO: ensure assumptions of translateTerm
    val propString = Main.translateTerm(prop)
    output.println(s"-- Axiom $name: ${prop.pretty(ctxt)}")
    output.println(s"axiom $fullName $argString: $propString")
    output.println()
  }
}
