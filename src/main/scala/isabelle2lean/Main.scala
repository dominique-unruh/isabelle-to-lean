package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.*
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.pure.Proofterm.PThm
import Naming.mapName
import Globals.{ctxt, output, stopWatch, given}
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

// TODO: Is shareCommonData useful? `PolyML.shareCommonData PolyML.rootFunction` or `ML_Heap.share_common_data` or similar?

//noinspection UnstableApiUsage
object Main {
  // Note: We can get all theorems from a thy (incl ancestors) via "Global_Theory.all_thms_of thy false"
  private val thmNames = Seq(
//          "HOL.conjI",
        "Nat.add_0_right",
//          "Binomial.binomial_eq_0",
  )

  def await[A](awaitable: Awaitable[A]): A = Await.result(awaitable, Duration.Inf)

  def defineConstant(name: String, typ: String, body: String, noncomputable: Boolean = false): Unit = {
    defineConstant(name, List((typ, body)))
  }

  def defineConstant(name: String, defs: List[(String,String)]): Unit = {
    val definitions = defs map { case (typ,body) => Constant.Definition(name, ITyp.parse(typ), Cord(body)) }
    await(Constants.add(name, Constant.createConstant(
      name = name, output = output, definitions = definitions)))
  }


  def main(args: Array[String]): Unit = {
    Globals.isabelle.await

    Globals.stopWatch.stop()
    println("Isabelle initialized after: " + Globals.stopWatch.formatTime())
    Globals.stopWatch.reset()
    Globals.stopWatch.start()

    output.synchronized {
      output.println(preamble)
      output.println()
    }

    defineConstant("Pure.imp", "prop => prop => prop", "fun p q => p -> q")
    defineConstant("Pure.prop", "prop => prop", "fun p => p")
//    defineConstant("Pure.eq", "???", "fun p q => p = q")
//    defineConstant("HOL.eq", "???", "fun p q => (Classical.propDecidable (p = q)).decide", noncomputable = true)
//    defineConstant("Pure.all", "???", "fun f => ∀x, f x")
//    defineConstant("HOL.All", "???", "fun f => (Classical.propDecidable (∀x, f x = true)).decide", noncomputable = true)
    defineConstant("HOL.Trueprop", "bool => prop", "fun b => b = true")
    defineConstant("HOL.conj", "bool => bool => bool", "and")
    defineConstant("HOL.disj", "bool => bool => bool", "or")
    defineConstant("HOL.implies", "bool => bool => bool", "fun a b => (!a) || b")
    defineConstant("HOL.Not", "bool => bool", "not")
    defineConstant("HOL.True", "bool", "Bool.true")
    defineConstant("HOL.False", "bool", "Bool.false")
    defineConstant("Nat.Suc", "nat => nat", "Nat.succ")
    defineConstant("Groups.plus_class.plus", List(
      "nat => nat => nat" -> "Nat.add",
      "int => int => int" -> "Nat.add",
    ))

    val futures = thmNames map { thmName =>
      for (thm <- Thm(ctxt, thmName).forceFuture;
           pthm = Utils.getPThm(thm);
           theorem <- Theorems.compute(pthm))
      yield
        println(s"### Finished $thmName")
    }

    for (future <- futures)
      Await.result(future, Duration.Inf)

    println(s"Done.")
    Utils.printStats()

    output.synchronized {
      output.close()
    }

    Globals.executor.shutdown()
  }

  def preamble: String =
//    IOUtils.toString(getClass.getResource("/preamble.lean"), "utf-8")
    Files.readString(Paths.get("src/main/lean/preamble.lean"))
}
