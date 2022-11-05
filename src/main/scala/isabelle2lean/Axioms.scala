package isabelle2lean

import de.unruh.isabelle.pure.Term

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

import Globals.given

object Axioms {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Future[Axiom]]()

  def add(name: String, axiom: Future[Axiom]): Future[Unit] =
    if (nameMap.putIfAbsent(name, axiom) != null)
      throw new RuntimeException("Double add")
    for (axiomNow <- axiom)
      yield assert(name == axiomNow.name)

  def compute(name: String, prop: Term): Future[Axiom] =
    for (concreteProp <- Future.successful(prop.concreteRecursive); // TODO: there should be a non-blocking variant of this
         result <- nameMap.computeIfAbsent(name, _ => Axiom.createAxiom(name, concreteProp, Globals.output, proofs = Nil)))
      yield {
        assert(prop == result.prop, (prop, result.prop))
        result
      }
}
