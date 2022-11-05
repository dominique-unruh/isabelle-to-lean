package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.Typ

case class ValueVariable(fullName: String, typ: ITyp) {
  def identifier: Identifier =
    Identifier(fullName)
  def outputTerm: OutputTerm =
    TypeConstraint(identifier, typ.outputTerm)

  def substitute(subst: TypSubstitution)(implicit isabelle: Isabelle): ValueVariable = 
    ValueVariable(fullName, subst.substitute(typ))
}
