package isabelle2lean

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.MLValue
import de.unruh.isabelle.pure.{MLValueTerm, MLValueTyp, TFree, TVar, Typ, Type}

import scala.concurrent.ExecutionContext.Implicits.given
import de.unruh.isabelle.mlvalue.Implicits.given
import de.unruh.isabelle.pure.Implicits.given
import isabelle2lean.Naming.mapName

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import Globals.given
import scalaz.{Cord, Show}

final class ITyp private(val uniqueHashCode: Hash, mlValue: MLValue[Typ])(implicit isabelle: Isabelle) {
  override def hashCode: Int = uniqueHashCode.hashCode
  override def equals(that: Any): Boolean = that match
    case that : ITyp => this.uniqueHashCode == that.uniqueHashCode
    case _ => false
  lazy val outputTerm: OutputTerm = ITyp.translateTyp(typ)
  lazy val pretty: String = MLValueTyp(mlValue).pretty(Globals.ctxt)
  inline def typ: MLValueTyp = MLValueTyp(mlValue)
  override def toString: String = pretty
}

object ITyp {
  given Show[ITyp] with
    override def show(typ: ITyp): Cord = Cord(typ.pretty)

  def apply(typ: MLValue[Typ])(implicit isabelle: Isabelle): ITyp = {
    val hash = Hash(IsabelleOps.uniqueHashCodeTyp(typ).retrieveNow)
    lookups.incrementAndGet()
    cache.computeIfAbsent(hash, {_ => misses.incrementAndGet(); new ITyp(hash, typ)})
  }
  def apply(typ: Typ)(implicit isabelle: Isabelle): ITyp = ITyp(typ.mlValue)

  /** Assumptions: no TVars or TFree have same name but different types */
  // TODO check
  private def translateTyp(typ: Typ): OutputTerm = typ match {
    case Type("fun", t1, t2) => FunType(translateTyp(t1), translateTyp(t2))
    case Type("fun", _*) => throw new RuntimeException("should not happen")
    case Type(tcon, typs@_*) => Application(Identifier(mapName(tcon, category = Namespace.TypeCon)),
      typs.map(translateTyp): _*)
    case TVar(name, index, sort) => Identifier(mapName(name = name, extra = index, category = Namespace.TVar))
    case TFree(name, sort) => Identifier(mapName(name, category = Namespace.TFree))
  }

  def parse(string: String): ITyp = ITyp(Typ(Globals.ctxt, string))

  private val cache = new ConcurrentHashMap[Hash, ITyp]()
  private val lookups = new AtomicInteger
  private val misses = new AtomicInteger
  def printStats(): Unit =
    println(s"ITyp stats: ${misses.get}/${lookups.get}")
}
