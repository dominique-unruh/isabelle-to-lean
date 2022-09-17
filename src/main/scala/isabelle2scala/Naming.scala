package isabelle2scala

object Naming {
  // TODO avoid conflicts between categories
  def quote(name: String, prefix: String = "", category: Namespace): String =
    prefix + name.replace('.', '_').replace('\'', '_')
}
