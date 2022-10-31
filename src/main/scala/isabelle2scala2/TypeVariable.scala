package isabelle2scala2

import de.unruh.isabelle.pure.Typ

case class TypeVariable(fullName: String, typ: Typ) {
  def outputTerm: OutputTerm =
    Identifier(fullName)
}
