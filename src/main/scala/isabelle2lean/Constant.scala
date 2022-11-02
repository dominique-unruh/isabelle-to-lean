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
import isabelle2lean.Constant.{Definition, lookups1, lookups2, misses}

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

case class Constant(typeFullName: String, name: String, typ: ITyp,
                    typParams: List[TypeVariable], definitions: List[Definition]) {
  override def toString: String = s"Const($name)"

  def typArgsFromTyp(typ: ITyp): List[ITyp] =
    IsabelleOps.constTypargs(Globals.thy, name, typ.typ).retrieveNow
      .map(ITyp.apply)

  override def equals(obj: Any): Boolean = ???

  override def hashCode(): Int = ???

/*  def instantiate(typArgs: List[ITyp]): Future[Instantiated] = {
    lookups2.incrementAndGet()
    cache.computeIfAbsent(typArgs, { _ =>
      misses.incrementAndGet()
      Future {
        if (name == "Groups.plus_class.plus") {
          println(s"instantiating $this with ${typArgs.map(_.pretty)}")
        }
        val fullName = Naming.mapName(name = name, extra = typArgs, category = Namespace.ConstantInstantiated)
        Instantiated(fullName = fullName, typ = typ, typArgs = typArgs)
      }})
  }*/

  inline def atIdentifier: Identifier = Identifier(typeFullName, at = true)

  private val cache = new ConcurrentHashMap[ITyp, Instantiated]()

  def instantiate(typ: ITyp) : Instantiated = {
    lookups1.incrementAndGet()
    cache.computeIfAbsent(typ, { _ =>
      misses.incrementAndGet()
      val typArgs = typArgsFromTyp(typ) // TODO: Those could be computed inside the Instantiated, possibly lazily
      // We wrap this into Future otherwise the call to `instantiate` raises a "recursive update" exception
      val fullName = Naming.mapName(name = name, extra = typ, category = Namespace.ConstantInstantiated)
      Instantiated(fullName = fullName, typ = typ, typArgs = typArgs)
    })
  }

  case class Instantiated(fullName: String, typ: ITyp, typArgs: List[ITyp]) {
    inline def constant: Constant.this.type = Constant.this

    override def hashCode(): Int = fullName.hashCode

    override def equals(obj: Any): Boolean = obj match
      case inst : Instantiated => fullName == inst.fullName
      case _ => false

    def substitute(subst: IterableOnce[(TypeVariable, ITyp)]): Future[Instantiated] =
      for (typ2 <- Utils.substituteTyp(typ, subst);
           inst = Constant.this.instantiate(typ2))
        yield inst

    lazy val definitionMatch: Option[Identifier] = {
      if (name == "Groups.plus_class.plus") {
        println(s"const-typ: ${Constant.this.typ.pretty}, my typ: ${typ.pretty}")
      }
      val matchingDefinitions =
        for (definition <- definitions;
             m <- definition.matches(typ))
        yield m
      matchingDefinitions match {
        case List() => None
        case List(m) => Some(m)
        case _ =>
          throw new AssertionError(s"Colliding definitions for $name: $matchingDefinitions")
      }
    }

    def isDefined: Boolean = definitionMatch.nonEmpty

    def asParameterTerm: OutputTerm = {
      assert(!isDefined)
      TypeConstraint(identifier,
        Application(constant.atIdentifier, typArgs.map(_.outputTerm): _*))
    }

    lazy val asUsageTerm: OutputTerm =
      definitionMatch match
        case Some(identifier) => identifier
          //    Application(Identifier(defName, at = true),
          //      typArgs.map(_.outputTerm): _*)
        case None => identifier

    inline def identifier: Identifier = {
      assert(!isDefined)
      Identifier(fullName)
    }
  }
}

object Constant {

  /** A definition of the constant, possibly at a smaller type */
  case class Definition(name: String, typ: ITyp, body: Cord) {
    val fullName: String = Naming.mapName(name = name, extra = typ, category = Namespace.ConstantDef)

    def matches(specificType: ITyp): Option[Identifier] = {
      // TODO: actually do a pattern match
      if (name == "Groups.plus_class.plus") {
        println(s"def typ: ${typ.pretty}, comparison: ${specificType == typ}")
      }
      if (specificType == typ)
        Some(atIdentifier)
      else
        None
    }

    def atIdentifier: Identifier = Identifier(fullName, at = true)
  }

  def createConstant(name: String, output: PrintWriter, definitions: List[Definition] = Nil) : Future[Constant] = {
    val typeFullName: String = Naming.mapName(name = name, category = Namespace.ConstantType)

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
        for (definition <- definitions) {
          output.println(cord"/-- Def of Isabelle constant $name :: ${typ.pretty}, at type ${definition.typ.pretty} -/")
          output.println(cord"noncomputable def ${definition.fullName} : ${definition.typ.outputTerm}")
          output.println(cord"  := ${definition.body}")
          output.println()
        }
        output.flush()
      }
      Constant(name = name, typ = typ, typParams = typParams, typeFullName = typeFullName,
        definitions = definitions)
    }
  }

  private val lookups1 = new AtomicInteger
  private val lookups2 = new AtomicInteger
  private val misses = new AtomicInteger

  def printStats(): Unit =
    println(s"Instantiated constant stats: ${misses.get}/${lookups1.get}+${lookups2.get}")
}
