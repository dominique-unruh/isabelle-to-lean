package isabelle2scala

import de.unruh.isabelle.pure.Term
import Globals.ctxt

import scala.collection.mutable
import Globals.given

import java.util.concurrent.ConcurrentHashMap

object Axioms {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Axiom]()

  def compute(name: String, prop: Term): Axiom =
    nameMap.computeIfAbsent(name, _ => actuallyCompute(name, prop))

  private def actuallyCompute(name: String, prop: Term): Axiom = {
    val axiom = isabelle2scala.Axiom(name = name, prop = prop)
    axiom.print(Globals.output)
    println(s"Printed axiom: $name: ${prop.pretty(ctxt)}")
    axiom
  }
}
