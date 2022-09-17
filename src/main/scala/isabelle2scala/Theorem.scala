package isabelle2scala

import de.unruh.isabelle.pure.Proofterm.PThm

//noinspection UnstableApiUsage
case class Theorem(pthm: PThm) extends LogicalEntity {
  override def toString: String = s"Theorem(${pthm.header.name}@${pthm.header.serial})"

  val fullName: String = Naming.quote(name = pthm.header.name, category = Namespace.Theorem)
}
