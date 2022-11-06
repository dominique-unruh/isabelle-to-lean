package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.{Context, Theory}
import isabelle2lean.Constant.ManualDefinition
import org.apache.commons.lang3.SystemUtils
import org.apache.commons.lang3.time.StopWatch

import java.io.{FileOutputStream, PrintWriter}
import java.nio.file.Path
import java.util.concurrent.{ExecutorService, Executors, ThreadPoolExecutor}
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}
import scala.jdk.CollectionConverters.given

object Globals {
  val executor: ThreadPoolExecutor = Executors.newCachedThreadPool().asInstanceOf[ThreadPoolExecutor]
  implicit val executionContext: ExecutionContext = scala.concurrent.ExecutionContext.fromExecutor(executor)
  //  implicit val executionContext: ExecutionContext = scala.concurrent.ExecutionContext.global

  val stopWatch: StopWatch = StopWatch.createStarted()

  val isabelleHome: Path =
    if SystemUtils.IS_OS_WINDOWS
    then Path.of("c:/Programs/Isabelle2022")
    else Path.of("/opt/Isabelle2022")

  val setup: Isabelle.Setup = Isabelle.Setup(
    isabelleHome = isabelleHome, logic = "HOL-Proofs", executionContext = Globals.executionContext)
  Utils runAsDaemon {
    while (true) {
      Thread.sleep(10000)
//      Utils.printStats()
    }
  }


  implicit val isabelle: Isabelle = new Isabelle(setup)
  implicit val thy: Theory = Theory("Main")
  implicit val ctxt: Context = Context(thy).setMode(Context.Mode.schematic)
  val outputDir: Path = Path.of("target/lean")
  /** Synchronize printing via [[output]]. */
  val output = new PrintWriter(new FileOutputStream(outputDir.resolve("test.lean").toFile))

  val tryToParallelize = true

  val config: Config = Config(
    definitions = List(
      ManualDefinition("Pure", "Pure.imp", "prop => prop => prop", "fun p q => p -> q"),
      ManualDefinition("Pure", "Pure.prop", "prop => prop", "fun p => p"),
      ManualDefinition("Pure", "Pure.eq", "?'a::{} => ?'a => prop", "fun p q => p = q"),
      ManualDefinition("HOL.HOL", "HOL.eq", "?'a::{} => ?'a => bool", "fun p q => (Classical.propDecidable (p = q)).decide"),
      ManualDefinition("Pure", "Pure.all", "(?'a::{} => prop) => prop", "fun f => ∀x, f x"),
      ManualDefinition("HOL.HOL", "HOL.Trueprop", "bool => prop", "fun b => b = true"),
      ManualDefinition("HOL.HOL", "HOL.implies", "bool => bool => bool", "fun a b => (!a) || b"),
      ManualDefinition("HOL.Groups", "Groups.plus_class.plus", "int => int => int", "Int.add"),
      ManualDefinition("HOL.HOL", "HOL.The", "(?'a::{} => bool) => ?'a",
        "fun P => let inst : Nonempty _a0 := sorry; Classical.epsilon (fun x => P x = true)") // TODO avoid sorry by adding typeclass
  ))
}
