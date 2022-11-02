package isabelle2lean

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
import Utils.given
import org.apache.commons.lang3.time.StopWatch
import scalaz.Cord

//noinspection UnstableApiUsage
object Main {
  def getPThm(thm: Thm): PThm = {
    @tailrec
    def strip(prf: Proofterm): PThm = prf match {
      case Proofterm.AppP(proof1, _) => strip(proof1)
      case Proofterm.Appt(proof, _) => strip(proof)
      case prf: Proofterm.PThm => prf
      case prf => throw new AssertionError(s"getPThm: unexpected proofterm $prf")
    }

    strip(thm.proofOf)
  }

  def await[A](awaitable: Awaitable[A]): A = Await.result(awaitable, Duration.Inf)

  def defineConstant(name: String, body: String, noncomputable: Boolean = false): Unit =
    await(Constants.add(name, Constant.createConstant(
      name = name, output = output, definition = Some(Cord(body)), noncomputable = noncomputable)))


  def main(args: Array[String]): Unit = {
    val stopWatch = StopWatch.createStarted()

    // We can get all theorems from a thy (incl ancestors) via "Global_Theory.all_thms_of thy false"
    val thmNames = Seq(
//      "HOL.conjI",
//      "Binomial.binomial_eq_0",
      "Nat.add_0_right",
    )


    Globals.isabelle.await

    stopWatch.stop()
    println("Isabelle initialized after: " + stopWatch.formatTime())
    stopWatch.reset()
    stopWatch.start()

    output.synchronized {
      output.println(preamble)
      output.println()
    }

    defineConstant("Pure.imp", "fun p q => p -> q")
    defineConstant("Pure.prop", "fun p => p")
    defineConstant("Pure.eq", "fun p q => p = q")
    defineConstant("HOL.eq", "fun p q => (Classical.propDecidable (p = q)).decide", noncomputable = true)
    defineConstant("Pure.all", "fun f => ∀x, f x")
    defineConstant("HOL.All", "fun f => (Classical.propDecidable (∀x, f x = true)).decide", noncomputable = true)
    defineConstant("HOL.Trueprop", "fun b => b = true")
    defineConstant("HOL.conj", "and")
    defineConstant("HOL.disj", "or")
    defineConstant("HOL.implies", "fun a b => (!a) || b")
    defineConstant("HOL.Not", "not")
    defineConstant("HOL.True", "Bool.true")
    defineConstant("HOL.False", "Bool.false")
    defineConstant("Nat.Suc", "Nat.succ")

    val futures = thmNames map { thmName =>
      for (thm <- Thm(ctxt, thmName).forceFuture;
           pthm = getPThm(thm);
           theorem <- Theorems.compute(pthm))
      yield {
        println(s"### Finished $thmName")
        println(s"# theorems:       ${Theorems.count}")
        println(s"# axioms:         ${Axioms.count}")
        println(s"# constants:      ${Constants.count}")
      }}

    for (future <- futures)
      Await.result(future, Duration.Inf)

    println(s"Done. ${Globals.executor.getActiveCount}")
    ITyp.printStats()
    stopWatch.stop()
    System.out.println("Total time: " + stopWatch.formatTime())

    output.synchronized {
      output.close()
    }

    Globals.executor.shutdown()
  }

  def preamble: String =
//    IOUtils.toString(getClass.getResource("/preamble.lean"), "utf-8")
    Files.readString(Paths.get("src/main/lean/preamble.lean"))
}
