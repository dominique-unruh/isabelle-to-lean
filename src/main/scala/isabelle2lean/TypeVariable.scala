package isabelle2lean

import de.unruh.isabelle.pure.Typ

case class TypeVariable(fullName: String, typ: Typ) {
  def identifier: Identifier =
    Identifier(fullName)

  def outputTerm: OutputTerm =
    TypeConstraint(identifier, Identifier.Type)
}
