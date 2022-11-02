package isabelle2lean

import scala.language.implicitConversions

import de.unruh.isabelle.pure.{TVar, Typ}
import Globals.given
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given

import java.io.PrintWriter
import scala.concurrent.Future
import Globals.{ctxt, given}
import scalaz.Cord
import scalaz.syntax.show.cordInterpolator
import Utils.given_Conversion_String_Cords

// TODO Use ITyp
case class Constant(typeFullName: String, defFullName: Option[String], name: String, typ: ITyp, typArgs: List[TypeVariable]) {
  override def toString: String = s"Const($name)"

  def isDefined: Boolean = defFullName.nonEmpty

  def typArgsFromTyp(typ: ITyp): List[ITyp] =
    IsabelleOps.constTypargs(Globals.thy, name, typ.typ).retrieveNow
      .map(ITyp.apply)

  override def equals(obj: Any): Boolean = ???

  override def hashCode(): Int = ???

  // TODO: Use a cache of instantiations
  def instantiate(typArgs: List[ITyp]): Instantiated = {
    val fullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.ConstantInstantiated)
    Instantiated(fullName = fullName, typ = typ, typArgs = typArgs)
  }

  inline def atIdentifier: Identifier = Identifier(typeFullName, at = true)

  // TODO: Use a cache of instantiations
  def instantiate(typ: ITyp) : Instantiated =
    instantiate(typArgsFromTyp(typ))

  case class Instantiated(fullName: String, typ: ITyp, typArgs: List[ITyp]) {
    inline def constant: Constant.this.type = Constant.this

    override def hashCode(): Int = fullName.hashCode

    override def equals(obj: Any): Boolean = obj match
      case inst : Instantiated => fullName == inst.fullName
      case _ => false

    def substitute(subst: IterableOnce[(TypeVariable, ITyp)]): Future[Instantiated] =
      for (typArgs2 <- Utils.substituteTypArgs(typArgs, subst))
        yield Constant.this.instantiate(typArgs2)

    def asParameterTerm: OutputTerm =
      TypeConstraint(identifier,
        Application(constant.atIdentifier, typArgs.map(_.outputTerm): _*))

    def asUsageTerm: OutputTerm = defFullName match
      case Some(defName) =>
        Application(Identifier(defName, at = true),
          typArgs.map(_.outputTerm) :_*)
      case None => identifier

    inline def identifier: Identifier = Identifier(fullName)
  }
}

object Constant {
  def createConstant(name: String, output: PrintWriter, definition: Option[Cord] = None,
                     /** Only used when definition is given via [[definition]]. */
                     noncomputable: Boolean = false) : Future[Constant] = {
    val typeFullName: String = Naming.mapName(name = name, category = Namespace.ConstantType)
    val defFullName = if (definition.isEmpty) None
      else Some(Naming.mapName(name = name, category = Namespace.ConstantDef))

    for (typ0 <- IsabelleOps.theConstType(Globals.thy, name).retrieve;
         typParams0 <- IsabelleOps.constTypargs(Globals.thy, name, typ0).retrieve)
    yield {
      val typ = ITyp(typ0)
      val typParams = typParams0 map {
        case typ @ TVar(name, index, sort) =>
          //      assert(sort.isEmpty, sort)
          val name2 = Naming.mapName(name = name, extra = index, category = Namespace.TVar)
          TypeVariable(name2, typ = typ)
        case typ => throw new AssertionError(s"createConstant: $typ")
      }
      val typParamString = if (typParams.isEmpty)
        Cord.monoid.zero
      else
        Cord(" ") ++ Utils.parenList(typParams.map(_.outputTerm))

      output.synchronized {
        output.println(cord"/-- Type of Isabelle constant $name :: ${typ.pretty} -/")
        output.println(cord"def $typeFullName $typParamString := ${typ.outputTerm}")
        output.println()
        if (definition.nonEmpty) {
          output.println(cord"/-- Def of Isabelle constant $name :: ${typ.pretty} -/")
          output.println(cord"${if (noncomputable) "noncomputable " else Cord.monoid.zero}def ${defFullName.get}$typParamString : $typeFullName $typParamString")
          output.println(cord"  := ${definition.get}")
          output.println()
        }
        output.flush()
      }
      Constant(name = name, typ = typ, typArgs = typParams, typeFullName = typeFullName,
        defFullName = defFullName)
    }
  }
}
