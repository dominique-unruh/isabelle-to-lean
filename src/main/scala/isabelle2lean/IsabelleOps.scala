package isabelle2lean

import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.pure.{Term, Theory, Typ}

import Globals.given

//noinspection TypeAnnotation
object IsabelleOps {
  val addFrees = compileFunction[Term, List[(String, Typ)]]("fn t => Term.add_frees t []")
  val addVars = compileFunction[Term, List[((String, Int), Typ)]]("fn t => Term.add_vars t []")
  val addTFrees = compileFunction[Term, List[(String, List[String])]]("fn t => Term.add_tfrees t []")
  val addTVars = compileFunction[Term, List[((String, Int), List[String])]]("fn t => Term.add_tvars t []")
  val theConstType = compileFunction[Theory, String, Typ]("fn (thy,name) => Sign.the_const_type thy name")
  val constTypargs = compileFunction[Theory, String, Typ, List[Typ]]("fn (thy,name,typ) => Sign.const_typargs thy (name,typ)")
  val substituteTyp = compileFunction[List[(Typ,Typ)], Typ, Typ]("fn (subst, typ) => typ_subst_atomic subst typ")
  val substituteTypsInTerm = compileFunction[List[(Typ,Typ)], Term, Term]("fn (subst, term) => subst_atomic_types subst term")
  val uniqueHashCodeTyp = compileFunction[Typ, (Long, Long)](s"let\n${Hash.hashLib}\nin hashAsIntPair hashTyp end")
  // TODO: This is used only for ITyps, and often with equality general=specific. Make a wrapper that shortcuts in case of equality, using a ITyp.equals
  val typMatch = compileFunction[Theory, Typ, Typ, Option[List[(String, Int, Typ)]]](
    "fn (thy,general,specific) => Sign.typ_match thy (general,specific) Vartab.empty " +
      "|> Vartab.dest |> map (fn ((name,index),(sort,typ)) => (name,index,typ)) |> SOME " +
      "handle Type.TYPE_MATCH => NONE")
  // TODO: This is used only for ITyps, and often with equality general=specific. Make a wrapper that shortcuts in case of equality, using a ITyp.equals
  val typListMatch = compileFunction[Theory, List[(Typ,Typ)], Option[List[(String, Int, Typ)]]](
    "fn (thy, general_specific) => fold (Sign.typ_match thy) general_specific Vartab.empty " +
      "|> Vartab.dest |> map (fn ((name,index),(sort,typ)) => (name,index,typ)) |> SOME " +
      "handle Type.TYPE_MATCH => NONE")
  val getConstantsOf = compileFunction[Theory, List[(String, Typ)]](
    """fn thy => let
      |  val thy_name = Context.theory_name thy
      |  val {const_space, constants, ...} = Sign.consts_of thy |> Consts.dest
      |  in constants
      |      |> map_filter (fn (_, (_, SOME _)) => NONE
      |                      | (name, (typ, NONE)) =>
      |                         if thy_name =  Name_Space.the_entry_theory_name const_space name
      |                         then SOME (name, typ) else NONE)
      |  end
      |""".stripMargin)
  val theoryLongName = compileFunction[Theory, String]("Context.theory_long_name")
  val parentsOf = compileFunction[Theory, List[String]]("fn thy => Context.parents_of thy |> map Context.theory_long_name")
  val theoryOfConstant = compileFunction[Theory, String, String]("fn (thy, const) => Name_Space.the_entry_theory_name (Sign.consts_of thy |> Consts.space_of) const")
  val getAxiomsOf = compileFunction[Theory, List[(String, Term)]](
    """fn thy => let
      |  val thy_name = Context.theory_name thy
      |  val axiom_space = Theory.axiom_space thy
      |  in Theory.all_axioms_of thy
      |      |> map_filter (fn (name, prop) =>
      |                         if thy_name =  Name_Space.the_entry_theory_name axiom_space name
      |                         then SOME (name, prop) else NONE)
      |  end
      |""".stripMargin)
}
