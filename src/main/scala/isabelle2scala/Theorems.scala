package isabelle2scala

import de.unruh.isabelle.pure.Proofterm.PThm
import Globals.ctxt
import de.unruh.isabelle.pure.Proofterm
import scala.collection.mutable

import scala.concurrent.ExecutionContext.Implicits.given
import Globals.given

//noinspection UnstableApiUsage
object Theorems {
  type Serial = Long

  def count: Int = serialMap.size

  def namedCount: Int = nameMap.size

  private val serialMap = mutable.HashMap[Serial, Theorem]()
  private val nameMap = mutable.HashMap[String, Serial]()

  def compute(pthm: PThm): Theorem = serialMap.get(pthm.header.serial) match {
    case Some(theorem) => theorem
    case None =>
      val theorem = actuallyCompute(pthm)
      serialMap.put(pthm.header.serial, theorem) match {
        case None =>
        case Some(_) =>
          throw new RuntimeException("serial already there")
      }
      if (pthm.header.name != "") {
        nameMap.get(pthm.header.name) match {
          case Some(old) =>
            val oldProp = serialMap(old).pthm.header.prop
            val prop = pthm.header.prop
            println(s"*** isabelle2scala.Theorem ${pthm.header.name} already encountered ***")
            println(s"  $old: ${oldProp.pretty(ctxt)}")
            println(s"  ${pthm.header.serial}: ${prop.pretty(ctxt)}")
            if (prop != oldProp)
              println("  Propositions differ!")
          case None =>
            nameMap.put(pthm.header.name, pthm.header.serial)
        }
      }
      theorem
  }

  def actuallyCompute(pthm: PThm): Theorem = {
    val theorem = Theorem(pthm = pthm)
    theorem.print(Globals.output)
    println(s"Printed theorem ${theorem.name}: ${theorem.prop.pretty(ctxt)}")
    theorem
  }

}
