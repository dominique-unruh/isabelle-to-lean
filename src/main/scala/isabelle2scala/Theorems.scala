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
    serialMap.computeIfAbsent(pthm.header.serial, { _ => Future { // Putting inside a future here to avoid "Recursive update" error
      val theorem = actuallyCompute(pthm)
      addToNameMap(pthm, theorem)
      theorem}.flatten })

  private def addToNameMap(pthm: Proofterm.PThm, eventualTheorem: Future[Theorem]): Future[Unit] = Future {
    if (pthm.header.name != "") {
      val old = nameMap.putIfAbsent(pthm.header.name, eventualTheorem)
      if (old != null)
        for (oldTheorem <- old) {
          val oldProp = oldTheorem.pthm.header.prop
          val prop = pthm.header.prop
          print(s"*** Theorem ${pthm.header.name} already encountered ***\n" +
            s"  ${oldTheorem.pthm.header.serial}: ${oldProp.pretty(ctxt)}\n" +
            s"  ${pthm.header.serial}: ${prop.pretty(ctxt)}\n" +
            (if (prop != oldProp) "Propositions differ!\n" else ""))
        }
      else
        Future.unit
    } else
      Future.unit
  }

  def actuallyCompute(pthm: PThm): Future[Theorem] = {
    val theorem = Theorem(pthm = pthm)
    for (_ <- theorem.print(Globals.output);
         _ = println(s"Printed theorem ${theorem.name}: ${theorem.prop.pretty(ctxt)}"))
    yield theorem
  }
}
