package isabelle2scala2

import de.unruh.isabelle.pure.Term
import scalaz.{Cord, Show}
import scalaz.Scalaz.cordInterpolator
import scalaz.Cord

import scala.language.implicitConversions
import OutputTerm.given

sealed trait OutputTerm {
  def toCord: Cord
  override def toString: String = toCord.shows

  protected def maybeParens(term: OutputTerm, parens: Boolean): Cord =
    if (parens) cord"($term)" else term.toCord
}
object OutputTerm {
  implicit object showTerm extends Show[Term] {
    override def show(f: Term): Cord = Cord(Term.toString)
  }
  implicit object showOutputTerm extends Show[OutputTerm] {
    override def show(f: OutputTerm): Cord = f.toCord
  }
  // There is scalaz.std.StringInstances.stringInstance but that encloses strings in "".
  implicit object showString extends Show[String] {
    override def show(f: String): Cord = Cord(f)
    override def shows(f: String): String = f
  }
}

case class Comment(comment: String, term: OutputTerm) extends OutputTerm {
  assert(!comment.contains("/-"))
  assert(!comment.contains("-/"))
  override def toCord: Cord = cord"/-$comment-/ $term"
}

case class Identifier(name: String, at: Boolean = false) extends OutputTerm {
  override def toCord: Cord = if (at) cord"@$name" else Cord(name)
}

case class Application(head: OutputTerm, arg: OutputTerm) extends OutputTerm {
  override def toCord: Cord = {
    val headNoParens = head.isInstanceOf[Identifier] || head.isInstanceOf[Application] || head.isInstanceOf[Wildcard.type]
      || head.isInstanceOf[Parentheses]
    val argNoParens = arg.isInstanceOf[Identifier] || arg.isInstanceOf[Wildcard.type] || arg.isInstanceOf[Parentheses]
    cord"${maybeParens(head, !headNoParens)} ${maybeParens(arg, !argNoParens)}"
  }
}
object Application {
  def apply(head: OutputTerm, args: OutputTerm*): OutputTerm =
    args.foldLeft(head)(new Application(_,_))
}

case class Abstraction(variable: String, typ: OutputTerm, body: OutputTerm) extends OutputTerm {
  override def toCord: Cord = {
    val bodyNoParens = body.isInstanceOf[Identifier] || body.isInstanceOf[Application] || body.isInstanceOf[Abstraction] || body.isInstanceOf[Wildcard.type]
      || body.isInstanceOf[Parentheses]
    cord"fun ${TypeConstraint(Identifier(variable), typ).toCord} => ${maybeParens(body, !bodyNoParens)}"
  }
}

case class FunType(inType: OutputTerm, outType: OutputTerm) extends OutputTerm {
  override def toCord: Cord = {
    val inNoParens = inType.isInstanceOf[Identifier] || inType.isInstanceOf[Application] || inType.isInstanceOf[Wildcard.type]
      || inType.isInstanceOf[Parentheses]
    val outNoParens = outType.isInstanceOf[Identifier] || outType.isInstanceOf[Application] || outType.isInstanceOf[FunType] || outType.isInstanceOf[Wildcard.type]
      || outType.isInstanceOf[Parentheses]
    cord"${maybeParens(inType, !inNoParens)} -> ${maybeParens(outType, !outNoParens)}"
  }
}

case class TypeConstraint(value: OutputTerm, typ: OutputTerm) extends OutputTerm {
  override def toCord: Cord = {
    val valueNoParens = value.isInstanceOf[Identifier] || value.isInstanceOf[Application] || value.isInstanceOf[Wildcard.type]
      || value.isInstanceOf[Parentheses]
    val typNoParens = typ.isInstanceOf[Identifier] || typ.isInstanceOf[Application] || typ.isInstanceOf[FunType]
      || typ.isInstanceOf[Parentheses]
    cord"${maybeParens(value, !valueNoParens)}: ${maybeParens(typ, !typNoParens)}"
  }
}

case object Wildcard extends OutputTerm {
  override val toCord: Cord = Cord("_")
}

case class Parentheses(value: OutputTerm) extends OutputTerm {
  override def toCord: Cord = {
    val noParens = value.isInstanceOf[Parentheses]
    maybeParens(value, !noParens)
  }
}