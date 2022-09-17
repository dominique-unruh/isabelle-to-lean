package isabelle2scala

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.Proofterm.PThm
import de.unruh.isabelle.pure.*

import java.io.{FileOutputStream, PrintWriter}
import java.nio.file.Path
import scala.annotation.tailrec
import scala.collection.mutable
import Globals.{ctxt, output, given}

import concurrent.ExecutionContext.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import isabelle2scala.Naming.mapName

//noinspection UnstableApiUsage
object Main {
  def getPThm(thm: Thm): PThm = {
    @tailrec
    def strip(prf: Proofterm): PThm = prf match {
      case Proofterm.AppP(proof1, _) => strip(proof1)
      case Proofterm.Appt(proof, _) => strip(proof)
      case prf: Proofterm.PThm => prf
    }

    strip(thm.proofOf)
  }
  
  def main(args: Array[String]): Unit = {
    // We can get all theorems from a thy (incl ancestors) via "Global_Theory.all_thms_of thy false"
//    val thmName = "HOL.conjI"
    val thmName = "Binomial.binomial_eq_0"

    val thm = Thm(ctxt, thmName)
    val pthm = getPThm(thm)

    Constants.add(Constant("Pure.imp"))
    Constants.add(Constant("Pure.eq"))
    Constants.add(Constant("Pure.all"))

    output.println(preamble)
    Theorems.compute(pthm)

    println(s"# theorems:       ${Theorems.count}")
    println(s"# named theorems: ${Theorems.namedCount}")
    println(s"# axioms:         ${Axioms.count}")
    println(s"# constants:      ${Constants.count}")

    output.close()
  }

  // TODO: check for duplicate Var/Free with different types
  // TODO: check for duplicate TFree/TVar with different sorts
  def argumentsOfProp(prop: Term): String = {
    val vars = IsabelleOps.addVars(prop).retrieveNow.reverse
    val frees = IsabelleOps.addFrees(prop).retrieveNow.reverse
    if (frees.nonEmpty)
      System.err.println(s"Warning: nonempty frees, not sure how to handle this: ${prop.pretty(ctxt)}")
    val tfrees = IsabelleOps.addTFrees(prop).retrieveNow.reverse
    val tvars = IsabelleOps.addTVars(prop).retrieveNow.reverse
    assert(tfrees.isEmpty)

    // TODO add [Inhabited <var>] for each tvar
    val targs = tvars map { case ((name, index), sort) =>
      // TODO: don't ignore sort!
      val name2 = mapName(name + index, category = Namespace.TVar)
      s"{$name2 : Type}"
    }

    val vars2 = vars map { case ((name, index), typ) =>
      val name2 = mapName(name + index, category = Namespace.Var)
      s"($name2 : ${translateTyp(typ)})"
    }

    val frees2 = frees map { case (name, typ) =>
      val name2 = mapName(name, category = Namespace.Free)
      s"(/-FREE-/ $name2 : ${translateTyp(typ)})"
    }

    (targs ++ vars2 ++ frees2).mkString(" ")
  }

  /** Assumption: no TVars or TFree have same name but different types
   * TODO: check this assm here */
  def translateTermClean(term: Term, env: List[String] = Nil): OutputTerm = translateTerm(cleanDuplicateAbsNames(term, used = env.toSet), env = env)

  /** Assumptions:
   * - no TVars or TFree have same name but different types
   * - no empty names in Abs or shadowed names */
  def translateTerm(term: Term, env: List[String]): OutputTerm = term match {
    case App(t, u) => Application({translateTerm(t, env)}, translateTerm(u, env))
    case Abs(name, typ, term) =>
      assert(name.nonEmpty)
      val name2 = mapName(name, category = Namespace.AbsVar)
      Abstraction(name2, translateTyp(typ), translateTerm(term, name2 :: env))
    case Bound(i) => Identifier(env(i))
    case Var(name, index, typ) => Identifier(mapName(s"$name$index", category = Namespace.Var))
    case Free(name, typ) => Identifier(mapName(name, category = Namespace.Free))
    case Const(name, typ) =>
      val const = Constants.compute(name)
      val args = const.instantiate(typ).map(translateTyp)
      Application(Identifier(const.fullName, at = true), args :_*)
  }

  /** Assumptions: no TVars or TFree have same name but different types */
  // TODO check
  def translateTyp(typ: Typ): OutputTerm = typ match {
    case Type("fun", t1, t2) => FunType(translateTyp(t1), translateTyp(t2))
    case Type("fun", _*) => throw new RuntimeException("should not happen")
    case Type(tcon, typs@_*) => Application(Identifier(mapName(tcon, category = Namespace.TypeCon)),
      typs.map(translateTyp) :_*)
    case TVar(name, index, sort) => Identifier(mapName(name + index, category = Namespace.TVar))
    case TFree(name, sort) => Identifier(mapName(name, category = Namespace.TFree))
  }

  val preamble: String =
    """def prop := Prop
      |def Pure_imp x y := x -> y
      |def Pure_eq {a: Type} (x y : a) := x = y
      |def Pure_all {_a0 : Type} (f: _a0 -> prop) := ∀x, f x
      |-- def Pure_prop (x: Prop) := x
      |def HOL_bool := Bool
      |axiom itself (a: Type) : Type
      |axiom Nat_nat : Type
      |axiom Set_set : Type -> Type
      |axiom Nat_ind : Type
      |axiom Num_num : Type
      |axiom Sum_Type_sum : Type -> Type -> Type
      |axiom Product_Type_unit : Type
      |axiom Product_Type_prod : Type -> Type -> Type
      |axiom Num_num_num_IITN_num : Type
      |axiom Int_int : Type
      |
      |""".stripMargin

  def cleanDuplicateAbsNames(term: Term, used: Set[String] = Set.empty): Term = {
    def getUnused(name: String): String = {
      var name2 = if (name.isEmpty) "x" else name
      while (used.contains(name2))
        name2 += '\''
      name2
    }
    term match
      case Const(_,_) | Free(_,_) | Var(_,_,_) | Bound(_) => term
      case App(t,u) =>
        val tClean = cleanDuplicateAbsNames(t, used)
        val uClean = cleanDuplicateAbsNames(u, used)
        if ((tClean eq t) && (uClean eq u))
          term
        else
          App(tClean, uClean)
      case Abs(x,typ,body) =>
        val x2 = getUnused(x)
        val bodyClean = cleanDuplicateAbsNames(body, used + x2)
        if ((x2 eq x) && (bodyClean eq body))
          term
        else
          Abs(x2,typ,bodyClean)
  }
}
