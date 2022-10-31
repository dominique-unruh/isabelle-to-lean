package isabelle2lean

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

import Globals.given

object Constants {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Future[Constant]]()

  def add(name: String, constant: Future[Constant]): Future[Unit] =
    if (nameMap.putIfAbsent(name, constant) != null)
      throw new RuntimeException("Double add")
    for (constantNow <- constant)
      yield assert(name == constantNow.name)

  def compute(name: String): Future[Constant] =
    nameMap.computeIfAbsent(name, _ => Constant.createConstant(name, Globals.output))
}
