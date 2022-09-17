package isabelle2scala

import de.unruh.isabelle.pure.{TVar, Term, Typ, Type}
import isabelle2scala.Globals.ctxt

import java.io.PrintWriter
import scala.collection.mutable
import Globals.given

import concurrent.ExecutionContext.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.Implicits.given

case class Constant(name: String) extends LogicalEntity {
  override def toString: String = s"Const($name)"

  private val nameMap = mutable.HashMap[String, Constant]()

  val fullName: String = Naming.mapName(name = name, category = Namespace.Constant)

  // TODO get correct type
  val typ: Typ = IsabelleOps.theConstType(Globals.thy, name).retrieveNow
  val typArgs: List[(String, Int)] = IsabelleOps.constTypargs(Globals.thy, name, typ).retrieveNow map {
    case TVar(name, index, sort) =>
//      assert(sort.isEmpty, sort)
      (name,index)
  }

  def print(output: PrintWriter): Unit = {
    val typString = Main.translateTyp(typ)
    val argString = typArgs map { case (name,index) =>
      val name2 = Naming.mapName(name + index, category = Namespace.TVar)
      s"{$name2 : Type}"
    } mkString " "

    output.println(s"-- Constant $name :: ${typ.pretty(ctxt)}")
    output.println(s"axiom $fullName $argString: $typString")
    output.println()
  }

  def instantiate(typ: Typ): List[Typ] =
    IsabelleOps.constTypargs(Globals.thy, name, typ).retrieveNow
}
