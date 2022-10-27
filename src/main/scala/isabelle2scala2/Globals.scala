package isabelle2scala2

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.{Context, Theory}

import java.io.{FileOutputStream, PrintWriter}
import java.nio.file.Path
import java.util.concurrent.{ExecutorService, Executors, ThreadPoolExecutor}
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}
import scala.jdk.CollectionConverters.given

object Globals {
  val setup: Isabelle.Setup = Isabelle.Setup(isabelleHome = Path.of("c:/Programs/Isabelle2022"), logic = "HOL-Proofs")
  val executor: ThreadPoolExecutor = Executors.newCachedThreadPool().asInstanceOf[ThreadPoolExecutor]
  Utils runAsDaemon {
    while (true) {
      val active = executor.getActiveCount
      val size = executor.getPoolSize
//      println()
      println(s"Executor: $active/$size")
//      println()

//      for ((thread: Thread) <- Thread.getAllStackTraces.asScala.keySet) {
//        println(s"${thread.getName}: ${thread.getPriority}, ${thread.isDaemon}, ${thread.isAlive}")
//      }
//      println()

      Thread.sleep(10000)
    }
  }
  implicit val executionContext: ExecutionContext = scala.concurrent.ExecutionContext.fromExecutor(executor)

//  implicit val executionContext: ExecutionContext = scala.concurrent.ExecutionContext.global

  implicit val isabelle: Isabelle = new Isabelle(setup)
  implicit val thy: Theory = Theory("Main")
  implicit val ctxt: Context = Context(thy)
  /** Synchronize printing via [[output]]. */
  val output = new PrintWriter(new FileOutputStream("test.lean"))
}