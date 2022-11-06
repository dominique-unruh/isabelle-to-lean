package isabelle2lean

import de.unruh.isabelle.pure.{TVar, Typ}

import Globals.isabelle

case class TypeVariable private (fullName: String, typ: ITyp) {
  def identifier: Identifier =
    Identifier(fullName)

  def outputTerm: OutputTerm =
    TypeConstraint(identifier, Identifier.Type)
}

object TypeVariable {
  def tvar(name: String, index: Int): TypeVariable = {
    val name2 = Naming.mapName(name = name, extra = index, category = Namespace.TVar)
    TypeVariable(fullName = name2, typ = ITyp(TVar(name, index, Nil)))
  }

//  def apply(typ: ITyp): TypeVariable = typ.typ match
//    case TVar(name, index, sort) => tvar(name, index)
}