package isabelle2lean

import de.unruh.isabelle.pure.{App, Const, Term, Theory, Typ}

import java.io.PrintWriter
import scala.concurrent.{Await, Future}
import Globals.{config, given}
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.{toplevelStateConverter, given}
import scalaz.Cord

import java.nio.file.Files
import scala.collection.mutable
import scala.concurrent.duration.Duration
import scala.sys.Prop

class ITheory private(name: String, val output: PrintWriter) {
  def println(text: Cord): Unit = output.synchronized { output.println(text.shows); output.flush() }
}

object ITheory {
  private def createDefinitions(axioms: List[(String, Term)], theory: String, output: PrintWriter): Unit = {
    // Manual definitions
    for (defi <- config.definitions
         if defi.theory == theory) {
      val constant = Constants.get(defi.constant)
      val typ = Typ(Globals.ctxt, defi.typ)
      val ityp = ITyp(typ)
      for (tvars <- IsabelleOps.addTVarsT(typ).retrieve;
           tfrees <- IsabelleOps.addTFreesT(typ).retrieve)
      yield {
        assert(tfrees.isEmpty)
        val typParams = tvars.map { case ((n, i), _) => TypeVariable.tvar(n, i) }
        constant.createDefinition(typ = ityp, body = Cord(defi.body), typParams = typParams, output = output)
      }
    }

    // Auto definitions
    def createDef(name: String, prop: Term) : Option[Boolean] =
      prop match {
        case App(App(Const("Pure.eq", _), Const(constName, typ)), body) =>
          println(s"Considering autogen for $constName ($name)")
          val ityp = ITyp(typ)
          val dependsOn = UniqueListBuffer.empty[Constant#Instantiated]
          Utils.translateTermClean(body, constants = dependsOn)
          if (dependsOn.nonEmpty) {
            println(s"Nope (depends on ${dependsOn.map(_.fullName).mkString(", ")})")
            None // means: has not been consumed, and nothing has changed
          } else {
            println(s"Looks good")
            val constant = Constants.get(constName)
            val typParams = Await.result(Utils.typParametersOfProp(prop), Duration.Inf)
            // TODO: check that all `this.typParams` occur in `ityp`
            constant.createDefinition(typ = ityp, body = Utils.translateTermClean(body).toCord, typParams = typParams, output = output)
            Some(true) // means: has been consumed and something has changed
          }
        case _ =>
          Some(false) // means: has been consumed and nothing has changed
      }

    var changed = true
    var axioms2 = axioms
    while (changed) {
      changed = false
      val axioms3 = new mutable.ListBuffer[(String, Term)]
      for (axiom <- axioms2)
        createDef(axiom._1, axiom._2) match
          case Some(thisChanged) =>
            changed = changed || thisChanged
          case None =>
            axioms3 += axiom
      axioms2 = axioms3.result()
    }
    println(s"Definitions that I could not create due to cyclicity: ${axioms2.map(_._1).mkString(", ")}")
    println(s"Definitions that I could not create due to other reasons: ???")

  }

  def createTheory(name: String): Future[ITheory] = {
    println(s"Starting theory $name")
    val outputFile = Globals.outputDir.resolve(s"${name.replace('.','/')}.lean")
    Files.createDirectories(outputFile.getParent)
    val output = new PrintWriter(outputFile.toFile, "utf-8")

    def outputHeader(parents: List[String]): Unit = {
      output.println(s"/- Theory $name, imported from Isabelle/HOL -/")
      output.println()
      output.println("import IsabelleHOL.IsabelleHOLPreamble")
      for (parent <- parents)
        output.println(s"import IsabelleHOL.AutoGen.$parent")
      output.println()
      output.println(
        """set_option linter.unusedVariables false
          |set_option autoImplicit false
          |""".stripMargin)
      output.println()
    }

    val thy = Theory(name)

    for (isabelleConstants <- IsabelleOps.getConstantsOf(thy).retrieve;
         thyLongName <- IsabelleOps.theoryLongName(thy).retrieve;
         _ = assert(thyLongName == name, (thyLongName, name));
         parents <- IsabelleOps.parentsOf(thy).retrieve;
         _ = outputHeader(parents);
         parentTheories <- Future.sequence(parents.map(Theories.compute));
         constants <- Future.sequence(isabelleConstants.map((constName, typ) =>
           Constant.createConstant(theory = name, name = constName, output = output, typ = ITyp(typ))));
         _ = for (constant <- constants) Constants.add(constant);
         isabelleAxioms <- IsabelleOps.getAxiomsOf(thy).retrieve;
         _ = createDefinitions(axioms = isabelleAxioms, output = output, theory = name);
         axioms <- Future.sequence(isabelleAxioms.map((axiomName, prop) =>
           Axiom.createAxiom(name = axiomName, prop = prop.concreteRecursive, output = output, theory = name))))
    yield {
      for (axiom <- axioms) Axioms.add(axiom)
      output.flush()
      println(s"Created $name")
      ITheory(name, output)
    }
  }
}
