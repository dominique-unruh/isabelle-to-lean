package isabelle2lean

import de.unruh.isabelle.pure.{TVar, Typ}

import Globals.isabelle

case class TypeVariable(fullName: String, typ: Typ) {
  def identifier: Identifier =
    Identifier(fullName)

  def outputTerm: OutputTerm =
    TypeConstraint(identifier, Identifier.Type)
}

object TypeVariable {
  def tvar(name: String, index: Int): TypeVariable = {
    val name2 = Naming.mapName(name = name, extra = index, category = Namespace.TVar)
    TypeVariable(fullName = name2, typ = TVar(name, index, Nil))
  }
}