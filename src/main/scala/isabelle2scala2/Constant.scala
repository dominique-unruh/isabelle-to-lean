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

  def typArgsFromTyp(typ: Typ): List[Typ] =
    IsabelleOps.constTypargs(Globals.thy, name, typ).retrieveNow

  def instantiate(typArgs: List[Typ]): Instantiated = {
    val fullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.ConstantInstantiated)
    Instantiated(fullName = fullName, typ = typ, typArgs = typArgs)
  }

  inline def identifier: Identifier = Identifier(fullName)
  inline def atIdentifier: Identifier = Identifier(fullName, at = true)

  def instantiate(typ: Typ) : Instantiated =
    instantiate(typArgsFromTyp(typ))

  case class Instantiated(fullName: String, typ: Typ, typArgs: List[Typ]) {
    inline def constant: Constant.this.type = Constant.this

    override def hashCode(): Int = fullName.hashCode

    override def equals(obj: Any): Boolean = obj match
      case inst : Instantiated => fullName == inst.fullName
      case _ => false

    def substitute(subst: IterableOnce[(TypeVariable, Typ)]): Future[Instantiated] =
      for (typArgs2 <- Utils.substituteTypArgs(typArgs, subst))
        yield Constant.this.instantiate(typArgs2)


    def outputTerm: OutputTerm =
      TypeConstraint(identifier,
        Application(constant.atIdentifier, typArgs.map(Utils.translateTyp): _*))

    inline def identifier: Identifier = Identifier(fullName)
  }
}

object Constant {
  def createConstant(name: String, output: PrintWriter) : Future[Constant] = {
    val fullName: String = Naming.mapName(name = name, category = Namespace.Constant)
    for (typ <- IsabelleOps.theConstType(Globals.thy, name).retrieve;
         typString = Utils.translateTyp(typ);
         typArgs: List[(String, Int)] = IsabelleOps.constTypargs(Globals.thy, name, typ).retrieveNow map {
           case TVar(name, index, sort) =>
             //      assert(sort.isEmpty, sort)
             (name, index)
           case t => throw new AssertionError(s"createConstant: $t")
         };
         argString = typArgs map { case (name, index) =>
           val name2 = Naming.mapName(name = name, extra = index, category = Namespace.TVar)
           s"($name2: Type)"
         } mkString " ")
    yield {
        output.synchronized {
          output.println(s"/-- Type of Isabelle constant $name :: ${typ.pretty(ctxt)} -/")
          output.println(s"def $fullName $argString := $typString")
          output.println()
          output.flush()
        }
        Constant(name = name, typ = typ, typArgs = typArgs, typString = typString, fullName = fullName)
      }
  }
}
