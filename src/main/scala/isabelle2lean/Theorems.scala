package isabelle2lean

import de.unruh.isabelle.pure.Proofterm.PThm
import de.unruh.isabelle.pure.Term
import isabelle2lean.Globals.given
import isabelle2lean.Theorem.Serial

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

//noinspection UnstableApiUsage
object Theorems {
  def count: Int = serialMap.size

//  private val nameMap = new ConcurrentHashMap[String, Future[Theorem]]()
  private val serialMap = new ConcurrentHashMap[Serial, Future[Theorem]]()

/*
  def add(constant: Constant): Unit =
    if (nameMap.putIfAbsent(constant.name, constant) != null)
      throw new RuntimeException("Double add")
*/

  def compute(pthm: PThm): Future[Theorem] =
    for (result <- serialMap.computeIfAbsent(pthm.header.serial, _ => Theorem.createTheorem(pthm, Globals.output)))
      yield {
        assert(pthm.header.serial == result.serial)
        result
      }
}
