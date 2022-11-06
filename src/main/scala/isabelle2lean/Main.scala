package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.*
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.pure.Proofterm.PThm
import Naming.mapName
import Globals.{ctxt, output, stopWatch, given}
import org.apache.commons.io.{FileUtils, IOUtils}

import java.io.{File, FileOutputStream, InputStreamReader, PrintWriter}
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
          "HOL.conjI",
//        "Nat.add_0_right",
//          "Binomial.binomial_eq_0",
  )



  def await[A](awaitable: Awaitable[A]): A = Await.result(awaitable, Duration.Inf)

  def defineConstant(name: String, typ: String, body: String): Unit = {
    defineConstant(name, List((typ, body)))
  }

  def defineConstant(name: String, defs: List[(String,String)]): Unit = {
    val constant = Constants.get(name)
    val theory = await(Theories.compute(constant.theoryName))
    for ((typ,body) <- defs) {
      constant.createDefinition(ITyp.parse(typ), Cord(body), Nil, theory.output)
    }
  }

  def defineConstant(name: String, typ: String, tparams: List[String], body: String): Unit = {
    val constant = Constants.get(name)
    val theory = await(Theories.compute(constant.theoryName))
    constant.createDefinition(typ = ITyp.parse(typ), body = Cord(body),
      typParams = tparams.map { name => TypeVariable.tvar(name, 0) },
      output = theory.output
    )
  }

  def proveAxiom(name: String, prop: String, tparams: List[String], body: String): Unit = {
    val axiom = Axioms.get(name)
    val theory = await(Theories.compute(axiom.theoryName))
    axiom.createProof(
      typArgs = tparams.map { name => TypeVariable.tvar(name, 0).typ },
      typParams = tparams.map { name => TypeVariable.tvar(name, 0) },
      body = Cord(body),
      output = theory.output)
  }


  def main(args: Array[String]): Unit = {
    Globals.isabelle.await

    Globals.stopWatch.stop()
    println("Isabelle initialized after: " + Globals.stopWatch.formatTime())
    Globals.stopWatch.reset()
    Globals.stopWatch.start()

    output.synchronized {
      output.println("""import IsabelleHOL.AutoGen.HOL.Nat
                       |set_option linter.unusedVariables false
                       |set_option autoImplicit false
                       |""".stripMargin)
      output.println()
    }

//    FileUtils.copyDirectory(new File("src/main/lean"), new File("target/lean"))
//    Files.writeString(Globals.outputDir.resolve("IsabelleHOLPreamble.lean"), preamble)

//    val pureThy = await(Theories.compute("Pure"))
//    val holThy = await(Theories.compute("HOL.HOL"))
    val natThy = await(Theories.compute("HOL.Nat"))

    println("Created theories")

    // TODO: get the prop argument from the theory
    proveAxiom("Pure.equal_elim", "⟦PROP ?A ≡ PROP ?B; PROP ?A⟧ ⟹ PROP ?B", Nil, "cast")
    proveAxiom("Pure.symmetric", "?x::?'a::{} ≡ ?y ⟹ ?y ≡ ?x", List("'a"), "Eq.symm")
    proveAxiom("Pure.reflexive", "?x::?'a::{} ≡ ?x", List("'a"), "Eq.refl x0")
    proveAxiom("Pure.combination", "⟦?f::?'a::{} => ?'b::{} ≡ ?g; ?x ≡ ?y⟧ ⟹ ?f ?x ≡ ?g ?y", List("'a", "'b"), "congr")
    proveAxiom("Pure.transitive", "⟦?x::?'a::{} ≡ ?y; ?y ≡ ?z⟧ ⟹ ?x ≡ ?z", List("'a"), "Eq.trans")

    println("Added proven axioms")

    val futures = thmNames map { thmName =>
      for (thm <- Thm(ctxt, thmName).forceFuture;
           pthm = Utils.getPThm(thm);
           theorem <- Theorems.compute(pthm))
      yield
        println(s"### Finished $thmName")
    }

    for (future <- futures)
      Await.result(future, Duration.Inf)

    Utils.printStats()

    output.synchronized {
      output.close()
    }

    Globals.executor.shutdown()

    println("****** Done ******")
  }

/*  def preamble: String =
//    IOUtils.toString(getClass.getResource("/IsabelleHOLPreamble.lean"), "utf-8")
    Files.readString(Paths.get("src/main/lean/IsabelleHOL/IsabelleHOLPreamble.lean"))*/
}
