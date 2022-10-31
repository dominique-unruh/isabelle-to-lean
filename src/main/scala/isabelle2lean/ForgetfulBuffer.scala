package isabelle2lean

import scala.collection.mutable

class ForgetfulBuffer[A] private() extends mutable.Buffer[A] {
  override def insertAll(idx: Int, elems: IterableOnce[A]): Unit = {}

  override def insert(idx: Int, elem: A): Unit = {}

  override def patch[B >: A](from: Int, other: IterableOnce[B], replaced: Int): mutable.Buffer[B] = ForgetfulBuffer.apply()

  override def patchInPlace(from: Int, patch: IterableOnce[A], replaced: Int): this.type = this

  override def prepend(elem: A): this.type = this

  override def remove(idx: Int): A = ???

  def remove(idx: Int, count: Int): Unit = {}

  override def length: Int = ???

  override def iterator: Iterator[A] = ???

  override def apply(i: Int): A = ???

  override def update(idx: Int, elem: A): Unit = {}

  def clear(): Unit = {}

  override def addOne(elem: A): this.type = this
}


object ForgetfulBuffer {
  private def instance = new ForgetfulBuffer[Nothing]()
  inline def apply[A](): ForgetfulBuffer[A] = instance.asInstanceOf[ForgetfulBuffer[A]]
}
