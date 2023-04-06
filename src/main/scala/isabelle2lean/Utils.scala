package isabelle2lean

import scala.language.implicitConversions
import de.unruh.isabelle.pure.{Abs, App, Bound, Const, Free, Proofterm, TFree, TVar, Term, Thm, Typ, Type, Var}
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import Globals.{stopWatch, given}
import isabelle2lean.Main.await
import isabelle2lean.Naming.mapName
import scalaz.{Cord, Monoid, Show}

import java.io.PrintWriter
import scala.collection.mutable
import scala.concurrent.{Await, Future}
import Utils.given
import de.unruh.isabelle.pure.Proofterm.PThm
import scalaz.Cord.CordInterpolator.Cords
import scalaz.Cord.show
import scalaz.syntax.all.ToShowOps
import scalaz.Scalaz.cordInterpolator

import scala.annotation.tailrec
import scala.concurrent.duration.Duration

object Utils {
  def runAsDaemon(task: => Any): Unit = {
    val thread = new Thread({ () => task }: Runnable)
    thread.setDaemon(true)
    thread.start()
  }

  // TODO: check for duplicate Var/Free with different types
  def valParametersOfProp(prop: Term): Future[List[ValueVariable]] = {
    def translateTyps[A](v: Seq[(A, Typ)]) = Future.traverse(v) { case (x, typ) =>
      for (typ2 <- Future.successful(ITyp(typ).outputTerm)) yield (x, typ2)
    }

    for (vars <- IsabelleOps.addVars(prop).retrieve;
//         vars2 <- translateTyps(vars);
         frees <- IsabelleOps.addFrees(prop).retrieve
//         frees2 <- translateTyps(frees)
         )
    yield {
      val vars3 = vars.reverse map { case ((name, index), typ) =>
        val name2 = mapName(name = name, extra = index, category = Namespace.Var)
        ValueVariable(fullName = name2, typ = ITyp(typ))
//        s"($name2: $typ)"
      }
      val frees3 = frees.reverse map { case (name, typ) =>
        val name2 = mapName(name, category = Namespace.Free)
        ValueVariable(fullName = name2, typ = ITyp(typ))
//        s"($name2: $typ)"
      }
      (frees3 ++ vars3) // .mkString(" ")
    }
  }


  // TODO: check for duplicate TFree/TVar with different sorts
  def typParametersOfProp(prop: Term): Future[List[TypeVariable]] =
    for (tfrees <- IsabelleOps.addTFrees(prop).retrieve;
         tvars <- IsabelleOps.addTVars(prop).retrieve)
    yield {
      assert(tfrees.isEmpty)

      /*val targs =*/ tvars.reverse map { case ((name, index), sort) =>
        // TODO: don't ignore sort!?
        assert(sort.isEmpty)
        TypeVariable.tvar(name, index)
      }
      //      targs.mkString(" ")
    }


  /** Return an ɑ-equivalent term that has no empty or shadowed bound variable names and avoids all names in `used`. */
  def cleanDuplicateAbsNames(term: Term, used: Set[String] = Set.empty): Term = {
    def getUnused(name: String): String = {
      var name2 = if (name.isEmpty) "x" else name
      while (used.contains(name2))
        name2 += '\''
      name2
    }

    term match
      case Const(_, _) | Free(_, _) | Var(_, _, _) | Bound(_) => term
      case App(t, u) =>
        val tClean = cleanDuplicateAbsNames(t, used)
        val uClean = cleanDuplicateAbsNames(u, used)
        if ((tClean eq t) && (uClean eq u))
          term
        else
          App(tClean, uClean)
      case Abs(x, typ, body) =>
        val x2 = getUnused(x)
        val bodyClean = cleanDuplicateAbsNames(body, used + x2)
        if ((x2 eq x) && (bodyClean eq body))
          term
        else
          Abs(x2, typ, bodyClean)
  }

  /** Assumptions:
   * - no TVars or TFree have same name but different types
   * - no empty names in Abs or shadowed names
   *
   * @param defaultAllBut If not None, specified Frees/Vars that should be replaced by an arbitrary fixed value (of the correct type) */
  def translateTerm(term: Term, env: List[String],
                    defaultAllBut: Option[(Set[(String, Int)], Set[String])],
                    constants: mutable.Buffer[Constant#Instantiated]): OutputTerm = term match {
    case App(t, u) => Application(
      translateTerm(t, env, defaultAllBut, constants),
      translateTerm(u, env, defaultAllBut, constants))
    case Abs(name, typ, term) =>
      assert(name.nonEmpty)
      val name2 = mapName(name, category = Namespace.AbsVar)
      Abstraction(name2, ITyp(typ).outputTerm, translateTerm(term, name2 :: env, defaultAllBut, constants))
    case Bound(i) => Identifier(env(i))
    case Var(name, index, typ) =>
      defaultAllBut match {
        case Some((vars, _)) if !vars.contains(name, index) =>
          Comment(s"?$name.$index", TypeConstraint(Identifier("Classical.ofNonempty"), ITyp(typ).outputTerm))
        case _ =>
          Identifier(mapName(name = name, extra = index, category = Namespace.Var))
      }
    case Free(name, typ) =>
      defaultAllBut match {
        case Some((_, frees)) if !frees.contains(name) =>
          Comment(name, TypeConstraint(Identifier("Classical.ofNonempty"), ITyp(typ).outputTerm))
        case _ =>
          Identifier(mapName(name, category = Namespace.Free))
      }
    case Const(name, typ) =>
      val const: Constant = Constants.get(name)
      val instantiated: const.Instantiated = const.instantiate(ITyp(typ))
      if (!instantiated.isDefined)
        constants += instantiated
      //      val args = const.instantiate(typ).map(translateTyp_OLD)
      //      Application(Identifier(const.fullName, at = true), args: _*)
      instantiated.asUsageTerm
  }

  /** Assumption: no TVars or TFree have same name but different types
   * TODO: check this assm here */
  def translateTermClean(term: Term, env: List[String] = Nil,
                         defaultAllBut: Option[(Set[(String, Int)], Set[String])] = None,
                         constants: mutable.Buffer[Constant#Instantiated] = ForgetfulBuffer()): OutputTerm =
    translateTerm(cleanDuplicateAbsNames(term, used = env.toSet), env = env, defaultAllBut = defaultAllBut, constants = constants)


  extension[A] (list: List[A]) {
    /** Like .zip but fails if lists have different lengths */
    def zipStrict[B](other: List[B]): List[(A, B)] = list match
      case head :: tail => other match
        case ohead :: otail => (head, ohead) :: tail.zipStrict(otail)
        case Nil => throw IllegalArgumentException("zipStrict: second list longer")
      case Nil => other match
        case _: `::`[_] => throw IllegalArgumentException("zipStrict: first list longer")
        case Nil => Nil
  }

  extension[A, B >: A : Show] (iterable: IterableOnce[A]) {
    def mkCord(sep: Cord): Cord = {
      var result = Cord.monoid.zero
      var first = true
      for (x <- iterable.iterator) {
        if (first)
          result = (x:B).show
        else
          result = result ++ sep ++ (x:B).show
        first = false
      }
      result
    }

    def mkCord(sep: String): Cord = mkCord(Cord(sep))
  }

/*  def substituteTyp(typ: ITyp, subst: IterableOnce[(TypeVariable, ITyp)]): Future[ITyp] = {
    val subst2: List[(Typ, Typ)] = subst.iterator.map { case (t, u) => (t.typ, u.typ) }.toList
    IsabelleOps.substituteTyp(subst2, typ.typ).retrieve
      .map(ITyp.apply)
  }*/

  /*def substituteTypArgs(typArgs: List[ITyp], subst: IterableOnce[(TypeVariable, ITyp)]): Future[List[ITyp]] = {
    val subst2: List[(Typ, Typ)] = subst.iterator.map { case (t, u) => (t.typ, u.typ) }.toList
    val typArgs2 = typArgs.map(arg => IsabelleOps.substituteTyp(subst2, arg.typ).retrieve)
    Future.sequence(typArgs2)
      .map(_.map(ITyp.apply))
  }*/

  def parenList(terms: Iterable[OutputTerm], parens: String = "()", sep: String = " ", prefix: String = " "): Cord =
    if (terms.isEmpty) Cord.monoid.zero
    else {
      if (parens == "()")
        Cord(prefix) ++ terms.iterator.map(Parentheses(_).toCord).mkCord(sep)
      else {
        val open = Cord(parens.substring(0,1))
        val close = Cord(parens.substring(1,2))
        Cord(prefix) ++ terms.iterator.map(t => cord"$open$t$close").mkCord(sep)
      }
    }

  given Conversion[String, Cords] with
    inline def apply(string: String): Cords = Cords.trivial(Cord(string))

  extension (string: String)
    inline def toCord = Cord(string)

  def printStats(): Unit = {
    println()
    val active = Globals.executor.getActiveCount
    val size = Globals.executor.getPoolSize
    println(s"Executor: $active/$size")
    ITyp.printStats()
    Constant.printStats()
    Axiom.printStats()
    println(s"Theorems/axioms/constants: ${Theorems.count}/${Axioms.count}/${Constants.count}")
    stopWatch.split()
    System.out.println("Elapsed: " + stopWatch.formatTime())
    stopWatch.unsplit()
    println()
  }


  //noinspection UnstableApiUsage
  def getPThm(thm: Thm): PThm = {
    @tailrec
    def strip(prf: Proofterm): PThm = prf match {
      case Proofterm.AppP(proof1, _) => strip(proof1)
      case Proofterm.Appt(proof, _) => strip(proof)
      case prf: Proofterm.PThm => prf
      case prf => throw new AssertionError(s"getPThm: unexpected proofterm $prf")
    }

    strip(thm.proofOf)
  }

  def printto(output: PrintWriter, text: Cord): Unit = output.synchronized {
    output.println(text.shows)
  }


  def hasSorts(term: Term): Boolean = {
    val found = for ((v, sort) <- IsabelleOps.addTVars(term).retrieveNow ++ IsabelleOps.addTFrees(term).retrieveNow;
                     if sort.nonEmpty)
    yield {
      println(s"has sort: $v, $sort in $term")
      ()
    }
    found.nonEmpty
  }
}