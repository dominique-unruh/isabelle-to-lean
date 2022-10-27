package isabelle2scala2

import de.unruh.isabelle.pure.{TVar, Typ}
import Globals.given
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given

import java.io.PrintWriter
import scala.concurrent.Future
import Globals.{ctxt, given}

case class Constant(fullName: String, name: String, typ: Typ, typString: OutputTerm, typArgs: List[(String, Int)]) {
  override def toString: String = s"Const($name)"

  def instantiate(typ: Typ): List[Typ] =
    IsabelleOps.constTypargs(Globals.thy, name, typ).retrieveNow
}

object Constant {
  def createConstant(name: String, output: PrintWriter) : Future[Constant] = {
    val fullName: String = Naming.mapName(name = name, category = Namespace.Constant)
    for (typ <- IsabelleOps.theConstType(Globals.thy, name).retrieve;
         typString = Main.translateTyp_OLD(typ);
         typArgs: List[(String, Int)] = IsabelleOps.constTypargs(Globals.thy, name, typ).retrieveNow map {
           case TVar(name, index, sort) =>
             //      assert(sort.isEmpty, sort)
             (name, index)
         };
         argString = typArgs map { case (name, index) =>
           val name2 = Naming.mapName((name, index), category = Namespace.TVar)
           s"{$name2 : Type}"
         } mkString " ")
    yield {
        output.synchronized {
          output.println(s"-- Constant $name :: ${typ.pretty(ctxt)}")
          output.println(s"axiom $fullName $argString: $typString")
          output.println()
          output.flush()
        }
        Constant(name = name, typ = typ, typArgs = typArgs, typString = typString, fullName = fullName)
      }
  }
}
