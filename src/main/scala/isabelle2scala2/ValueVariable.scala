package isabelle2scala2

import de.unruh.isabelle.pure.Typ

case class ValueVariable(fullName: String, typ: Typ) {
  def identifier: Identifier =
    Identifier(fullName)
  def outputTerm: OutputTerm =
    TypeConstraint(identifier, Utils.translateTyp(typ))
}
