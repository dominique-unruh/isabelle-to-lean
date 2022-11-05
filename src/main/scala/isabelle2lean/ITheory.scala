package isabelle2lean

import de.unruh.isabelle.pure.Theory

import java.io.PrintWriter
import scala.concurrent.Future
import Globals.given
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import scalaz.Cord

import java.nio.file.Files

class ITheory private(name: String, output: PrintWriter) {
  def println(text: Cord): Unit = output.synchronized { output.println(text.shows); output.flush() }
}

object ITheory {
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
