package isabelle2scala

import scala.collection.mutable

object Constants {
  def count: Int = nameMap.size

  private val nameMap = mutable.HashMap[String, Constant]()

  def compute(name: String): Constant = nameMap.get(name) match {
    case Some(constant) => constant
    case None =>
      val constant = actuallyCompute(name)
      nameMap.put(name, constant)
      constant
  }

  private def actuallyCompute(name: String): Constant = {
    println(s"Computing constant: $name: $name")
    val constant = Constant(name)
    constant
  }
}
