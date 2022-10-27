package isabelle2scala2

import de.unruh.isabelle.pure.Term

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

import Globals.given

object Axioms {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Future[Axiom]]()

/*
  def add(constant: Constant): Unit =
    if (nameMap.putIfAbsent(constant.name, constant) != null)
      throw new RuntimeException("Double add")
*/

  def compute(name: String, prop: Term): Future[Axiom] =
    for (concreteProp <- Future.successful(prop.concreteRecursive); // TODO: there should be a non-blocking variant of this
         result <- nameMap.computeIfAbsent(name, _ => Axiom.createAxiom(name, concreteProp, Globals.output)))
      yield {
        assert(prop == result.prop)
        result
      }
}
