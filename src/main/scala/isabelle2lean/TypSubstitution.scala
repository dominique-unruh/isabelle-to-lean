package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.{Term, Typ}
import isabelle2lean.Utils.zipStrict

import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given

// TODO: make sure IsabelleOps.substituteTyp and `IsabelleOps.substituteTypsInTerm` are not used elsewhere, use only TypSubstitution

class TypSubstitution(subst: List[(Typ, Typ)]) {
  def substitute(typ: ITyp)(implicit isabelle: Isabelle): ITyp = ITyp(IsabelleOps.substituteTyp(subst, typ.typ))
  def substitute(term: Term)(implicit isabelle: Isabelle): Term = IsabelleOps.substituteTypsInTerm(subst, term).retrieveNow
}

object TypSubstitution {
  def apply(tvars: List[TypeVariable], replacement: List[ITyp]): TypSubstitution = new TypSubstitution(
    tvars.zipStrict(replacement).map { case (v,r) => (v.typ, r.typ) }
  )
}
