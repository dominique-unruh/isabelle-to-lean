package isabelle2lean

import scala.collection.mutable

class ForgetfulBuffer[A] private(check: Option[A => Unit] = None) extends mutable.Buffer[A] {
  override def insertAll(idx: Int, elems: IterableOnce[A]): Unit =
    for (c <- check; e <- elems) c(e)

  override def insert(idx: Int, elem: A): Unit =
    for (c <- check) c(elem)

  override def patch[B >: A](from: Int, other: IterableOnce[B], replaced: Int): mutable.Buffer[B] = ???

  override def patchInPlace(from: Int, patch: IterableOnce[A], replaced: Int): this.type = {
    for (c <- check; p <- patch) c(p)
    this
  }

  override def prepend(elem: A): this.type = {
    for (c <- check) c(elem)
    this
  }

  override def remove(idx: Int): A = ???

  def remove(idx: Int, count: Int): Unit = {}

  override def length: Int = ???

  override def iterator: Iterator[A] = ???

  override def apply(i: Int): A = ???

  override def update(idx: Int, elem: A): Unit =
    for (c <- check) c(elem)


  def clear(): Unit = {}

  override def addOne(elem: A): this.type = {
    for (c <- check) c(elem)
    this
  }
}


object ForgetfulBuffer {
  private def instance = new ForgetfulBuffer[Nothing]()
  inline def apply[A](): ForgetfulBuffer[A] = instance.asInstanceOf[ForgetfulBuffer[A]]
  @inline def apply[A](check: A => Unit) = new ForgetfulBuffer[A](Some(check))
}
