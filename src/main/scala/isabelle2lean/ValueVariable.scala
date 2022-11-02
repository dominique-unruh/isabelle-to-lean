package isabelle2lean

import de.unruh.isabelle.pure.Typ

case class ValueVariable(fullName: String, typ: ITyp) {
  def identifier: Identifier =
    Identifier(fullName)
  def outputTerm: OutputTerm =
    TypeConstraint(identifier, typ.outputTerm)
}
