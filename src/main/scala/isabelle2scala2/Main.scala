package isabelle2scala2

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.*
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.pure.Proofterm.PThm
import Naming.mapName
import Globals.{ctxt, output, given}
import org.apache.commons.io.IOUtils

import java.io.{FileOutputStream, InputStreamReader, PrintWriter}
import java.nio.file.{Files, Path, Paths}
import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Awaitable, Future}
import scala.jdk.CollectionConverters.given

//noinspection UnstableApiUsage
object Main {
  def getPThm(thm: Thm): PThm = { // TODO use futures
    @tailrec
    def strip(prf: Proofterm): PThm = prf match {
      case Proofterm.AppP(proof1, _) => strip(proof1)
      case Proofterm.Appt(proof, _) => strip(proof)
      case prf: Proofterm.PThm => prf
    }

    strip(thm.proofOf)
  }

  def await[A](awaitable: Awaitable[A]): A = Await.result(awaitable, Duration.Inf)

  def main(args: Array[String]): Unit = {
    // We can get all theorems from a thy (incl ancestors) via "Global_Theory.all_thms_of thy false"
    val thmNames = Seq(
      "HOL.conjI",
//      "Binomial.binomial_eq_0",
//      "Nat.add_0_right",
    )

    //    Constants.add(Constant("Pure.imp"))
    //    Constants.add(Constant("Pure.eq"))
    //    Constants.add(Constant("Pure.all"))

    output.synchronized {
      output.println(preamble
//        .replace("\n", "    ")
      )
      output.println()
    }

//    await(Constants.compute("Pure.imp"))
//    await(Constants.compute("Pure.eq"))

    val futures = thmNames map { thmName =>
      for (thm <- Thm(ctxt, thmName).forceFuture;
           pthm = getPThm(thm);
           theorem <- Theorems.compute(pthm))
      yield {
        println(s"### Finished $thmName")
//        println(s"### A.k.a. $theorem")
        println(s"# theorems:       ${Theorems.count}")
//        println(s"# named theorems: ${Theorems.namedCount}")
        println(s"# axioms:         ${Axioms.count}")
        println(s"# constants:      ${Constants.count}")
      }}

    for (future <- futures)
      Await.result(future, Duration.Inf)

    println(s"Done. ${Globals.executor.getActiveCount}")

//    Globals.executor.shutdown()

    output.synchronized {
      output.close()
    }

    Globals.executor.shutdown()
  }

  def preamble: String =
//    IOUtils.toString(getClass.getResource("/preamble.lean"), "utf-8")
    Files.readString(Paths.get("src/main/lean/preamble.lean"))

  // TODO: check for duplicate Var/Free with different types
  // TODO: check for duplicate TFree/TVar with different sorts
  // TODO use futures
  def argumentsOfProp_OLD(prop: Term): String = {
    val vars = IsabelleOps.addVars(prop).retrieveNow.reverse
    val frees = IsabelleOps.addFrees(prop).retrieveNow.reverse
    //    if frees.nonEmpty && vars.nonEmpty then
    //      System.err.println(s"Warning: nonempty vars and frees, not sure how to handle this: ${prop.pretty(ctxt)}")
    val tfrees = IsabelleOps.addTFrees(prop).retrieveNow.reverse
    val tvars = IsabelleOps.addTVars(prop).retrieveNow.reverse
    assert(tfrees.isEmpty)

    val targs = tvars map { case ((name, index), sort) =>
      // TODO: don't ignore sort!
      val name2 = mapName((name, index), category = Namespace.TVar)
      s"{$name2 : Type} [Nonempty $name2]"
    }

    val vars2 = vars map { case ((name, index), typ) =>
      val name2 = mapName((name, index), category = Namespace.Var)
      s"($name2 : ${translateTyp_OLD(typ)})"
    }

    val frees2 = frees map { case (name, typ) =>
      val name2 = mapName(name, category = Namespace.Free)
      s"($name2 : ${translateTyp_OLD(typ)})"
    }

    (targs ++ frees2 ++ vars2).mkString(" ")
  }


  /** Assumption: no TVars or TFree have same name but different types
   * TODO: check this assm here */
  def translateTermClean(term: Term, env: List[String] = Nil,
                         defaultAllBut: Option[(Set[(String, Int)], Set[String])] = None): OutputTerm =
    translateTerm(cleanDuplicateAbsNames(term, used = env.toSet), env = env, defaultAllBut = defaultAllBut)


  /** Assumptions:
   * - no TVars or TFree have same name but different types
   * - no empty names in Abs or shadowed names */
  def translateTerm(term: Term, env: List[String],
                    defaultAllBut: Option[(Set[(String, Int)], Set[String])]): OutputTerm = term match {
    case App(t, u) => Application({
      translateTerm(t, env, defaultAllBut)
    }, translateTerm(u, env, defaultAllBut))
    case Abs(name, typ, term) =>
      assert(name.nonEmpty)
      val name2 = mapName(name, category = Namespace.AbsVar)
      Abstraction(name2, translateTyp_OLD(typ), translateTerm(term, name2 :: env, defaultAllBut))
    case Bound(i) => Identifier(env(i))
    case Var(name, index, typ) =>
      defaultAllBut match {
        case Some((vars, _)) if !vars.contains(name, index) =>
          Comment(s"?$name.$index", TypeConstraint(Identifier("Classical.ofNonempty"), translateTyp_OLD(typ)))
        case _ =>
          Identifier(mapName((name, index), category = Namespace.Var))
      }
    case Free(name, typ) =>
      defaultAllBut match {
        case Some((_, frees)) if !frees.contains(name) =>
          Comment(name, TypeConstraint(Identifier("Classical.ofNonempty"), translateTyp_OLD(typ)))
        case _ =>
          Identifier(mapName(name, category = Namespace.Free))
      }
    case Const(name, typ) =>
      val const : Constant = await(Constants.compute(name))
      val args = const.instantiate(typ).map(translateTyp_OLD)
      Application(Identifier(const.fullName, at = true), args: _*)
  }

  /** Assumptions: no TVars or TFree have same name but different types */
  // TODO check
  def translateTyp_OLD(typ: Typ): OutputTerm = typ match {
    case Type("fun", t1, t2) => FunType(translateTyp_OLD(t1), translateTyp_OLD(t2))
    case Type("fun", _*) => throw new RuntimeException("should not happen")
    case Type(tcon, typs@_*) => Application(Identifier(mapName(tcon, category = Namespace.TypeCon)),
      typs.map(translateTyp_OLD): _*)
    case TVar(name, index, sort) => Identifier(mapName((name, index), category = Namespace.TVar))
    case TFree(name, sort) => Identifier(mapName(name, category = Namespace.TFree))
  }


  def cleanDuplicateAbsNames(term: Term, used: Set[String] = Set.empty): Term = {
    def getUnused(name: String): String = {
      var name2 = if (name.isEmpty) "x" else name
      while (used.contains(name2))
        name2 += '\''
      name2
    }

    term match
      case Const(_, _) | Free(_, _) | Var(_, _, _) | Bound(_) => term
      case App(t, u) =>
        val tClean = cleanDuplicateAbsNames(t, used)
        val uClean = cleanDuplicateAbsNames(u, used)
        if ((tClean eq t) && (uClean eq u))
          term
        else
          App(tClean, uClean)
      case Abs(x, typ, body) =>
        val x2 = getUnused(x)
        val bodyClean = cleanDuplicateAbsNames(body, used + x2)
        if ((x2 eq x) && (bodyClean eq body))
          term
        else
          Abs(x2, typ, bodyClean)
  }

}
