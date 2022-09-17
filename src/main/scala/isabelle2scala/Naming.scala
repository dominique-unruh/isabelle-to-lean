package isabelle2scala

import scala.collection.mutable

object Naming {
  private val names = new mutable.HashMap[(Namespace, String | (String, Long)), String]()
  private val assigned = new mutable.HashSet[String]()

  // TODO: direct support for indexnames ($name$index is not injective!)
  def mapName(name: String | (String, Long),
              prefix: String = "",
              suggestion: String = "",
              category: Namespace): String = names.get((category, name)) match {
    case Some(mappedName) => mappedName
    case None =>
      var name2 =
        if (suggestion.nonEmpty)
          suggestion
        else
          name match {
            case name: String => name
            case (name: String, index: Long) => s"$name$index"
          }
      var mappedName = prefix +
        name2.replace('.', '_')
          .replace('\'', '_')
          .replace('@', '_')
          .replace(':', '_')

      while (assigned.contains(mappedName))
        mappedName += '\''
      names.put((category, name), mappedName)
      assigned.add(mappedName)
      mappedName
  }
}
