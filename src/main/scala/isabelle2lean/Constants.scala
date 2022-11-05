package isabelle2lean

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable
import scala.concurrent.Future

import Globals.given

object Constants {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Constant]()

  /** Call only from ITheory.createTheory */
  def add(constant: Constant): Unit =
    if (nameMap.putIfAbsent(constant.name, constant) != null)
      throw new RuntimeException("Double add")

//  def compute(name: String): Future[Constant] =
//    nameMap.computeIfAbsent(name, _ => Constant.createConstant(name, Globals.output))

  def get(name: String): Constant = nameMap.get(name)
}
