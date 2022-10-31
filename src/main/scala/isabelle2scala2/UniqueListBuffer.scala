package isabelle2scala2

import scala.collection.generic.DefaultSerializable
import scala.collection.mutable.ListBuffer
import scala.collection.{IterableFactoryDefaults, SeqFactory, StrictOptimizedSeqFactory, StrictOptimizedSeqOps, mutable}

/** Not thread safe */
class UniqueListBuffer[A] extends mutable.AbstractBuffer[A]
  with mutable.SeqOps[A, UniqueListBuffer, UniqueListBuffer[A]]
  with StrictOptimizedSeqOps[A, UniqueListBuffer, UniqueListBuffer[A]]
  with mutable.ReusableBuilder[A, List[A]]
  with IterableFactoryDefaults[A, UniqueListBuffer]
  with DefaultSerializable {
  private val buffer = new ListBuffer[A]()
  private val seen = new mutable.HashMap[A, Unit]()

  override def iterableFactory: SeqFactory[UniqueListBuffer] = UniqueListBuffer

  private def freshFrom(xs: IterableOnce[A]): this.type = addAll(xs)

  def insert(idx: Int, elem: A): Unit = ???
  def insertAll(idx: Int, elems: IterableOnce[A]): Unit = ???
  def patchInPlace(from: Int, patch: IterableOnce[A], replaced: Int): this.type = ???
  def prepend(elem: A): this.type = ???
  def remove(idx: Int): A = ???
  def remove(idx: Int, count: Int): Unit = ???

  // Members declared in scala.collection.mutable.Builder
  def clear(): Unit = {
    buffer.clear()
    seen.clear()
  }
  def result(): List[A] = buffer.result()

  // Members declared in scala.Function1
  def apply(v1: Int): A = ???

  // Members declared in scala.collection.mutable.Growable
  def addOne  (elem: A): this.type = {
    seen.getOrElseUpdate(elem, buffer.addOne(elem))
    this
  }

  // Members declared in scala.collection.IterableOnce
  def iterator: Iterator[A] = buffer.iterator

  def length: Int = seen.size

  // Members declared in scala.collection.mutable.SeqOps
  def update(idx: Int, elem: A): Unit = ???
}

object UniqueListBuffer extends StrictOptimizedSeqFactory[UniqueListBuffer] {
  def from[A](coll: collection.IterableOnce[A]): UniqueListBuffer[A] = new UniqueListBuffer[A].freshFrom(coll)

  def newBuilder[A]: mutable.Builder[A, UniqueListBuffer[A]] = new mutable.GrowableBuilder(empty[A])

  def empty[A]: UniqueListBuffer[A] = new UniqueListBuffer[A]
}
