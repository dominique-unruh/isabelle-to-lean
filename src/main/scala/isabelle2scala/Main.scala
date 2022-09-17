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
import isabelle2scala.Naming.quote

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
    val thmName = "HOL.conjI"

    val thm = Thm(ctxt, thmName)
    val pthm = getPThm(thm)
    val prf = pthm.body.proofOpenMlValue.retrieveNow

    output.println(preamble)
    Theorems.compute(pthm)

    println(s"# theorems:       ${Theorems.count}")
    println(s"# named theorems: ${Theorems.namedCount}")
    println(s"# axioms:         ${Axioms.count}")

    output.close()
  }

  // TODO: check for duplicate Var/Free with different types
  // TODO: check for duplicate TFree/TVar with different sorts
  def argumentsOfProp(prop: Term): String = {
    val vars = IsabelleOps.addVars(prop).retrieveNow.reverse
    val frees = IsabelleOps.addFrees(prop).retrieveNow.reverse
    assert(frees.isEmpty)
    val tfrees = IsabelleOps.addTFrees(prop).retrieveNow.reverse
    val tvars = IsabelleOps.addTVars(prop).retrieveNow.reverse
    assert(tfrees.isEmpty)
    val targs = tvars map { case ((name, index), sort) =>
      // TODO: don't ignore sort!
      val name2 = quote(name + index, category = Namespace.TVar)
      s"{$name2 : Type}"
    }
    val args = vars map { case ((name, index), typ) =>
      val name2 = quote(name + index, category = Namespace.Var)
      s"($name2 : ${translateTyp(typ)})"
    }
    (targs ++ args).mkString(" ")
  }
  
  def translateTerm(term: Term, env: List[String] = Nil): String = term match {
    case App(t, u) => s"(${translateTerm(t, env)}) (${translateTerm(u, env)})"
    case Abs(name, typ, term) =>
      val name2 = quote(name, category = Namespace.AbsVar)
      s"fn ($name2 : ${translateTyp(typ)}) => ${translateTerm(term, name2 :: env)}"
    case Bound(i) => env(i)
    case Var(name, index, typ) => quote(s"$name$index", category = Namespace.Var)
    case Free(name, typ) => quote(name, category = Namespace.Free)
    case Const(name, typ) =>
      val const = Constants.compute(name)
      s"${const.fullName} : ${translateTyp(typ)}"
  }

  def translateTyp(typ: Typ): String = typ match {
    case Type("fun", t1, t2) => s"(${translateTyp(t1)}) -> ${translateTyp(t2)}"
    case Type("fun", _*) => throw new RuntimeException("should not happen")
    case Type(tcon, typs@_*) => (quote(tcon, category = Namespace.TypeCon) :: typs.toList.map("(" + translateTyp(_) + ")")).mkString(" ")
    case TVar(name, index, sort) => quote(name + index, category = Namespace.TVar)
    case TFree(name, sort) => quote(name, category = Namespace.TFree)
  }

  val preamble: String =
    """def prop := Prop
      |def Pure_imp x y := x -> y
      |def Pure_eq {a: Type} (x y : a) := x = y
      |def Pure_prop (x: Prop) := x
      |
      |""".stripMargin
}
