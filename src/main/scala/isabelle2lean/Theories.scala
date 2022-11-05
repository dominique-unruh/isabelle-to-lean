package isabelle2lean

import java.util.concurrent.ConcurrentHashMap
import scala.concurrent.Future

object Theories {
  private val nameMap = new ConcurrentHashMap[String, Future[ITheory]]()

  def compute(name: String): Future[ITheory] =
    nameMap.computeIfAbsent(name, _ => ITheory.createTheory(name))
}
