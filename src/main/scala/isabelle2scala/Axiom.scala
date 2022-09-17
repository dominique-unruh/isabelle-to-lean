package isabelle2scala

import de.unruh.isabelle.pure.Term

import java.io.PrintWriter

case class Axiom(name: String, prop: Term) extends LogicalEntity {
  override def toString: String = s"Axiom($name)"

  val fullName: String = Naming.quote(prefix = "axiom_", name = name, category = Namespace.Axiom)

  def print(output: PrintWriter): Unit = {
    output.println(s"axiom $fullName ${Main.argumentsOfProp(prop)}: ${Main.translateTerm(prop)}")
    output.println()
  }
}
