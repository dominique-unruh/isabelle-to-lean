package isabelle2scala

import scala.collection.mutable

object Constants {
  def count: Int = nameMap.size

  private val nameMap = mutable.HashMap[String, Constant]()

  def add(constant: Constant): Unit = {
    assert(!nameMap.contains(constant.name))
    nameMap.put(constant.name, constant)
  }

  def compute(name: String): Constant = nameMap.get(name) match {
    case Some(constant) => constant
    case None =>
      val constant = actuallyCompute(name)
      nameMap.put(name, constant)
      constant
  }

  private def actuallyCompute(name: String): Constant = {
    val constant = Constant(name)
    constant.print(Globals.output)
    println(s"Printed constant: $name")
    constant
  }
}
