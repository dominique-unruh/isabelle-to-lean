package isabelle2scala2

import de.unruh.isabelle.pure.{Term, Typ}
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import Globals.given
import isabelle2scala2.Naming.mapName

import scala.concurrent.Future

object Utils {
  def runAsDaemon(task: => Any): Unit = {
    val thread = new Thread({ () => task } : Runnable)
    thread.setDaemon(true)
    thread.start()
  }

  // TODO: check for duplicate Var/Free with different types
  def valArgumentsOfProp(prop: Term): Future[String] = {
    def translateTyps[A](v: Seq[(A, Typ)]) = Future.traverse(v) { case (x, typ) =>
      for (typ2 <- Future.successful(Main.translateTyp_OLD(typ))) yield (x, typ2) }
    for (vars <- IsabelleOps.addVars(prop).retrieve;
         vars2 <- translateTyps(vars);
         frees <- IsabelleOps.addFrees(prop).retrieve;
         frees2 <- translateTyps(frees))
      yield {
        val vars3 = vars2.reverse map { case ((name, index), typ) =>
          val name2 = mapName((name, index), category = Namespace.Var)
          s"($name2 : $typ)"
        }
        val frees3 = frees2.reverse map { case (name, typ) =>
          val name2 = mapName(name, category = Namespace.Free)
          s"($name2 : $typ)"
        }
        (frees3 ++ vars3).mkString(" ")
      }
  }

  // TODO: check for duplicate TFree/TVar with different sorts
  def typArgumentsOfProp(prop: Term): Future[String] =
    for (tfrees <- IsabelleOps.addTFrees(prop).retrieve;
         tvars <- IsabelleOps.addTVars(prop).retrieve)
    yield {
      assert(tfrees.isEmpty);

      val targs = tvars.reverse map { case ((name, index), sort) =>
        // TODO: don't ignore sort!
        val name2 = mapName((name, index), category = Namespace.TVar)
        s"{$name2 : Type} [Nonempty $name2]"
      }

      targs.mkString(" ")
    }
}
