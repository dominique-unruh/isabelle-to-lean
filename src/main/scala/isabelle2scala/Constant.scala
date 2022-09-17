package isabelle2scala

case class Constant(name: String) extends LogicalEntity {
  override def toString: String = s"Const($name)"

  val fullName: String = Naming.quote(name = name, category = Namespace.Constant)
}
