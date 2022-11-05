package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.{Context, Theory}
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
  val outputDir = Path.of("target/lean")
  /** Synchronize printing via [[output]]. */
  val output = new PrintWriter(new FileOutputStream(outputDir.resolve("test.lean").toFile))

  val tryToParallelize = true
}
