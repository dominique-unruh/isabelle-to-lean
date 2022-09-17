package isabelle2scala

sealed trait OutputTerm {
  protected def maybeParens(term: OutputTerm, parens: Boolean) =
    if (parens) s"($term)" else term.toString
}

case class Identifier(name: String, at: Boolean = false) extends OutputTerm {
  override def toString: String = if (at) "@"+name else name
}

case class Application(head: OutputTerm, arg: OutputTerm) extends OutputTerm {
  override def toString: String = {
    val headNoParens = head.isInstanceOf[Identifier] || head.isInstanceOf[Application]
    val argNoParens = arg.isInstanceOf[Identifier]
    maybeParens(head, !headNoParens) + " " + maybeParens(arg, !argNoParens)
  }
}
object Application {
  def apply(head: OutputTerm, args: OutputTerm*): OutputTerm =
    args.foldLeft(head)(new Application(_,_))
}

case class Abstraction(variable: String, typ: OutputTerm, body: OutputTerm) extends OutputTerm {
  override def toString: String =
    s"fun ${TypeConstraint(Identifier(variable), typ)} => $body"
}

case class FunType(inType: OutputTerm, outType: OutputTerm) extends OutputTerm {
  override def toString: String = {
    val inNoParens = inType.isInstanceOf[Identifier] || inType.isInstanceOf[Application]
    val outNoParens = outType.isInstanceOf[Identifier] || outType.isInstanceOf[Application] || outType.isInstanceOf[FunType]
    maybeParens(inType, !inNoParens) + " -> " + maybeParens(outType, !outNoParens)
  }
}

case class TypeConstraint(value: OutputTerm, typ: OutputTerm) extends OutputTerm {
  override def toString: String = {
    val valueNoParens = value.isInstanceOf[Identifier] || value.isInstanceOf[Application]
    val typNoParens = typ.isInstanceOf[Identifier] || typ.isInstanceOf[Application] || typ.isInstanceOf[FunType]
    maybeParens(value, !valueNoParens) + ": " + maybeParens(typ, !typNoParens)
  }
}