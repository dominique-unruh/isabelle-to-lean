package isabelle2scala

import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.{Term, Theory, Typ}

import concurrent.ExecutionContext.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import Globals.given

//noinspection TypeAnnotation
object IsabelleOps {
  val addFrees = compileFunction[Term, List[(String, Typ)]]("fn t => Term.add_frees t []")
  val addVars = compileFunction[Term, List[((String, Int), Typ)]]("fn t => Term.add_vars t []")
  val addTFrees = compileFunction[Term, List[(String, List[String])]]("fn t => Term.add_tfrees t []")
  val addTVars = compileFunction[Term, List[((String, Int), List[String])]]("fn t => Term.add_tvars t []")
  val theConstType = compileFunction[Theory, String, Typ]("fn (thy,name) => Sign.the_const_type thy name")
  val constTypargs = compileFunction[Theory, String, Typ, List[Typ]]("fn (thy,name,typ) => Sign.const_typargs thy (name,typ)")
}
