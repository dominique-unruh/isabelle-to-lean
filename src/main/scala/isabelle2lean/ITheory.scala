package isabelle2lean

import de.unruh.isabelle.pure.{App, Const, Term, Theory, Typ}

import java.io.PrintWriter
import scala.concurrent.Future
import Globals.{config, given}
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import scalaz.Cord

import java.nio.file.Files
import scala.sys.Prop

class ITheory private(name: String, val output: PrintWriter) {
  def println(text: Cord): Unit = output.synchronized { output.println(text.shows); output.flush() }
}

object ITheory {
  private def createDefinitions(axioms: List[(String, Term, Long)], theory: String, output: PrintWriter): Future[Unit] = {
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
    def createDef(name: String, prop: Term, serial: Long) =
      prop match {
        case App(App(Const("Pure.eq", _), Const(constName, typ)), body) =>
          println(s"Autogen def $constName, $name, $serial")
          val ityp = ITyp(typ)
          val constant = Constants.get(constName)
          for (typParams <- Utils.typParametersOfProp(prop))
            yield
              // TODO: check that all `this.typParams` occur in `ityp`
              constant.createDefinition(typ = ityp, body = Utils.translateTermClean(body).toCord, typParams = typParams, output = output)
        case _ =>
          Future.unit
      }

    def createDefs(axioms: List[(String, Term, Long)]): Future[Unit] = axioms match
      case ::((name, prop, serial), rest) => for (_ <- createDef(name, prop, serial); _ <- createDefs(rest)) yield {}
      case Nil => Future.unit

    // TODO: sorting by serial number does not work, unfortunately. :(
    createDefs(axioms.sortBy(_._3))
  }

  def createTheory(name: String): Future[ITheory] = {
    println(s"Starting theory $name")
    val outputFile = Globals.outputDir.resolve(s"IsabelleHOL/${name.replace('.','/')}.lean")
    Files.createDirectories(outputFile.getParent)
    val output = new PrintWriter(outputFile.toFile, "utf-8")

    def outputHeader(parents: List[String]): Unit = {
      output.println(s"/- Theory $name, imported from Isabelle/HOL -/")
      output.println()
      output.println("import IsabelleHOL.IsabelleHOLPreamble")
      for (parent <- parents)
        output.println(s"import IsabelleHOL.$parent")
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
         _ <- createDefinitions(axioms = isabelleAxioms, output = output, theory = name);
         axioms <- Future.sequence(isabelleAxioms.map((axiomName, prop, serial) =>
           Axiom.createAxiom(name = axiomName, prop = prop.concreteRecursive, output = output, theory = name))))
    yield {
      for (axiom <- axioms) Axioms.add(axiom)
      output.flush()
      println(s"Created $name")
      ITheory(name, output)
    }
  }
}
