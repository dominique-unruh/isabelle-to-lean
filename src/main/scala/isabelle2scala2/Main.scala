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
//      "HOL.conjI",
//      "Binomial.binomial_eq_0",
      "Nat.add_0_right",
    )

    /*

    def Pure_imp1 (p:Prop) (q:Prop): Prop := p -> q
    def Pure_prop1 (p:Prop): Prop := p
    def Pure_eqprop (p:Prop) (q:Prop): Prop := p = q
    #reduce axiom_Pure_equal_elim Pure_imp1 Pure_eqprop

    */

    Globals.isabelle.await

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
      val name2 = mapName(name = name, extra = index, category = Namespace.TVar)
      s"{$name2 : Type} [Nonempty $name2]"
    }

    val vars2 = vars map { case ((name, index), typ) =>
      val name2 = mapName(name = name, extra = index, category = Namespace.Var)
      s"($name2 : ${Utils.translateTyp(typ)})"
    }

    val frees2 = frees map { case (name, typ) =>
      val name2 = mapName(name, category = Namespace.Free)
      s"($name2 : ${Utils.translateTyp(typ)})"
    }

    (targs ++ frees2 ++ vars2).mkString(" ")
  }
}
