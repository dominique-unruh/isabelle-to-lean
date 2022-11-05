package isabelle2lean

import scala.language.implicitConversions
import de.unruh.isabelle.pure.{TVar, Typ}
import Globals.given
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given

import java.io.PrintWriter
import scala.concurrent.{Await, Future}
import Globals.{ctxt, given}
import scalaz.Cord
import scalaz.syntax.show.cordInterpolator
import Utils.given_Conversion_String_Cords
import isabelle2lean.Constant.{lookups1, lookups2, misses}

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable.ListBuffer
import scala.concurrent.duration.Duration

case class Constant(typeFullName: String, name: String, typ: ITyp,
                    typParams: List[TypeVariable], theoryName: String) {
  override def toString: String = s"Const($name)"

  private var definitions: List[Definition] = Nil

  def typArgsFromTyp(typ: ITyp): List[ITyp] =
    IsabelleOps.constTypargs(Globals.thy, name, typ.typ).retrieveNow
      .map(ITyp.apply)

  override def equals(obj: Any): Boolean = ???

  override def hashCode(): Int = ???
  
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

    lazy val definitionMatch: Option[OutputTerm] = {
      val matches = definitions.map(_.matches(typ)) // List of futures of optional results
      val matches2 = Await.result(Future.sequence(matches), Duration.Inf)
      val matches3 = matches2.flatten // List of results
      matches3 match {
        case List() => None
        case List(m) =>
          println(s"DEFINITION MATCH: ${Constant.this.name} @ ${typ.pretty} -> $m")
          Some(m)
        case _ =>
          throw new AssertionError(s"Colliding definitions for $name: $matches")
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

  /** A definition of the constant, possibly at a smaller type */
  case class Definition(typ: ITyp, body: Cord, typParams: List[TypeVariable]) {
    val fullName: String = Naming.mapName(name = name, extra = typ, category = Namespace.ConstantDef)

    def matches(specificType: ITyp): Future[Option[OutputTerm]] =
      for (m <- IsabelleOps.typMatch(Globals.thy, typ.typ, specificType.typ).retrieve)
        yield
          m match
            case None => None
            case Some(matchTyps) =>
              val matchTypMap = Map.from(matchTyps.map { case (name, index, typ) => TypeVariable.tvar(name, index) -> ITyp(typ) })
              val typArgs = typParams.map(matchTypMap)
              //              println(s"const: $name, deftyp: ${typ.pretty}, specific: ${specificType.pretty}, args: ${typArgs}, map: ${matchTypMap}")
              Some(Application(atIdentifier, typArgs.map(_.outputTerm): _*))

    def atIdentifier: Identifier = Identifier(fullName, at = true)
  }

  def createDefinition(typ: ITyp, body: Cord, typParams: List[TypeVariable], theory: ITheory): Definition = {
    val defTypParamString = Utils.parenList(typParams.map(_.outputTerm), prefix = " ")
    val definition = Definition(typ, body, typParams)
    theory.println(
      cord"""/-- Def of Isabelle constant $name :: ${typ.pretty}, at type ${typ.pretty} -/
noncomputable def ${definition.fullName}${defTypParamString} : ${typ.outputTerm}
:= ${definition.body}
""")
    synchronized { 
      definitions = definition :: definitions
      cache.clear() // We could also just filter out everything with !.isDefined
    }
    definition
  }
}

object Constant {

  def createConstant(theory: String, name: String, output: PrintWriter, typ: ITyp) : Future[Constant] = {
    val typeFullName: String = Naming.mapName(name = name, category = Namespace.ConstantType)

    // TODO: When called from ITheory, we already have the typ. Don't query again?
    for (/*typ0 <- IsabelleOps.theConstType(Globals.thy, name).retrieve;
         */typParams0 <- IsabelleOps.constTypargs(Globals.thy, name, typ.typ).retrieve)
    yield {
//      val typ = ITyp(typ0)
      val typParams = typParams0 map {
        case typ @ TVar(name, index, sort) =>
          assert(sort.isEmpty || sort == List("HOL.type"), sort)
          TypeVariable.tvar(name, index)
        case typ => throw new AssertionError(s"createConstant: $typ")
      }
      val typParamString = Utils.parenList(typParams.map(_.outputTerm), prefix=" ")

      output.synchronized {
        output.println(cord"/-- Type of Isabelle constant $name :: ${typ.pretty} -/")
        output.println(cord"def $typeFullName$typParamString := ${typ.outputTerm}")
        output.println()
        output.flush()
      }
      Constant(name = name, typ = typ, typParams = typParams, typeFullName = typeFullName, theoryName = theory)
    }
  }

  private val lookups1 = new AtomicInteger
  private val lookups2 = new AtomicInteger
  private val misses = new AtomicInteger

  def printStats(): Unit =
    println(s"Instantiated constant stats: ${misses.get}/${lookups1.get}+${lookups2.get}")
}
