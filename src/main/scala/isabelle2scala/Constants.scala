package isabelle2scala

import java.util.concurrent.ConcurrentHashMap
import scala.collection.mutable

object Constants {
  def count: Int = nameMap.size

  private val nameMap = new ConcurrentHashMap[String, Constant]()

  def add(constant: Constant): Unit =
    if (nameMap.putIfAbsent(constant.name, constant) != null)
      throw new RuntimeException("Double add")

  def compute(name: String): Constant =
    nameMap.computeIfAbsent(name, _ => actuallyCompute(name))

  private def actuallyCompute(name: String): Constant = {
    val constant = Constant(name)
    constant.print(Globals.output)
    println(s"Printed constant: $name")
    constant
  }
}
