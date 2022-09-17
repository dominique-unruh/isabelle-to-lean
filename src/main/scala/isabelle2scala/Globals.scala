package isabelle2scala

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.Context

import java.io.{FileOutputStream, PrintWriter}
import java.nio.file.Path
import scala.concurrent.ExecutionContext.Implicits.given

object Globals {
  val setup: Isabelle.Setup = Isabelle.Setup(isabelleHome = Path.of("c:/Programs/Isabelle2021-1"), logic = "HOL-Proofs")
  implicit val isabelle: Isabelle = new Isabelle(setup)
  implicit val ctxt: Context = Context("Main")
  val output = new PrintWriter(new FileOutputStream("test.lean"))
}
