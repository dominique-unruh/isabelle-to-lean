package isabelle2scala

import de.unruh.isabelle.pure.Term
import Globals.ctxt
import scala.collection.mutable

import Globals.given
import scala.concurrent.ExecutionContext.Implicits.given

object Axioms {
  def count: Int = nameMap.size

  private val nameMap = mutable.HashMap[String, Axiom]()

  def compute(name: String, prop: Term): Axiom = nameMap.get(name) match {
    case Some(axiom) =>
      assert(prop == axiom.prop)
      axiom
    case None =>
      val axiom = actuallyCompute(name, prop)
      nameMap.put(name, axiom)
      axiom
  }

  private def actuallyCompute(name: String, prop: Term): Axiom = {
    println(s"Computing axiom: $name: ${prop.pretty(ctxt)}")
    val axiom = isabelle2scala.Axiom(name = name, prop = prop)
    axiom.print(Globals.output)
    axiom
  }
}
