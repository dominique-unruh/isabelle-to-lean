package isabelle2lean

import de.unruh.isabelle.pure.Term

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

import Globals.given

object Axioms {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Axiom]()

  /** Only use from ITheory.createTheory */
  def add(axiom: Axiom): Unit =
    if (nameMap.putIfAbsent(axiom.name, axiom) != null)
      throw new RuntimeException("Double add")

/*
  // TODO: remove
  def compute(name: String, prop: Term): Future[Axiom] =
    for (concreteProp <- Future.successful(prop.concreteRecursive); // TODO: there should be a non-blocking variant of this
         result <- nameMap.computeIfAbsent(name, _ => Axiom.createAxiom(name = name, prop = concreteProp, output = Globals.output)))
      yield {
        assert(prop == result.prop, (prop, result.prop))
        result
      }
*/

  def get(name: String): Axiom = {
    val result = nameMap.get(name)
    assert(result != null, name)
    result
  }
}
