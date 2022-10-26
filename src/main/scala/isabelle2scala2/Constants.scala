package isabelle2scala2

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

object Constants {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Future[Constant]]()

/*
  def add(constant: Constant): Unit =
    if (nameMap.putIfAbsent(constant.name, constant) != null)
      throw new RuntimeException("Double add")
*/

  def compute(name: String): Future[Constant] =
    nameMap.computeIfAbsent(name, _ => Constant.createConstant(name, Globals.output))
}
