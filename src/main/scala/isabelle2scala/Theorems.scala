package isabelle2scala

import de.unruh.isabelle.pure.Proofterm.PThm
import Globals.ctxt
import de.unruh.isabelle.pure.Proofterm

import scala.collection.mutable
import Globals.given

import java.util.concurrent.ConcurrentHashMap
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future, blocking}

//noinspection UnstableApiUsage
object Theorems {
  type Serial = Long

  def count: Int = serialMap.size

  def namedCount: Int = nameMap.size

  private val serialMap = new ConcurrentHashMap[Serial, Future[Theorem]]()
  private val nameMap = new ConcurrentHashMap[String, Future[Theorem]]()

  def compute(pthm: PThm): Future[Theorem] =
    serialMap.computeIfAbsent(pthm.header.serial, { _ =>
      val theorem = actuallyCompute(pthm)
      addToNameMap(pthm, theorem)
      theorem})

  private def addToNameMap(pthm: Proofterm.PThm, eventualTheorem: Future[Theorem]): Future[Unit] = Future {
    if (pthm.header.name != "") {
      val old = nameMap.putIfAbsent(pthm.header.name, eventualTheorem)
      if (old != null)
        for (oldTheorem <- old) {
          val oldProp = oldTheorem.pthm.header.prop
          val prop = pthm.header.prop
          println(s"*** Theorem ${pthm.header.name} already encountered ***")
          println(s"  $old: ${oldProp.pretty(ctxt)}")
          println(s"  ${pthm.header.serial}: ${prop.pretty(ctxt)}")
          if (prop != oldProp)
            println("  Propositions differ!")
        }
      else
        Future.unit
    } else
      Future.unit
  }

  def actuallyCompute(pthm: PThm): Future[Theorem] = Future {
    val theorem = Theorem(pthm = pthm)
    theorem.print(Globals.output)
    println(s"Printed theorem ${theorem.name}: ${theorem.prop.pretty(ctxt)}")
    theorem
  }

}
