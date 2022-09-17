package isabelle2scala

import scala.collection.mutable

object Naming {
  private val names = new mutable.HashMap[(Namespace, String), String]()
  private val assigned = new mutable.HashSet[String]()

  // TODO: direct support for indexnames ($name$index is not injective!)
  def mapName(name: String, prefix: String = "", category: Namespace): String = names.get((category, name)) match {
    case Some(mappedName) => mappedName
    case None =>
      var mappedName = prefix +
        name.replace('.', '_')
          .replace('\'', '_')
          .replace('@', '_')
      while (assigned.contains(mappedName))
        mappedName += '\''
      names.put((category, name), mappedName)
      assigned.add(mappedName)
      mappedName
  }
}
