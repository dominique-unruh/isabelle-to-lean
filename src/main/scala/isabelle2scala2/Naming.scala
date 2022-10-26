package isabelle2scala2

import java.util.concurrent.ConcurrentHashMap
import scala.annotation.tailrec
import scala.collection.mutable
import scala.runtime.BoxedUnit
import scala.util.control.Breaks

object Naming {
  private val names = new ConcurrentHashMap[(Namespace, String | (String, Long)), String]()
  /** Synchronization via `this` */
  private val assigned = new ConcurrentHashMap[String, BoxedUnit]()

  def letterlike(c: Char): Boolean = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    || greek(c) || coptic(c) || letterlikeSymbols(c)
  def greek(c: Char): Boolean = ((c >= 'α' && c <= 'ω') || (c >= 'Α' && c <= 'Ω') || (c >= 'ἀ' && c <= '῾'))
    && (c != 'λ' && c != 'Π' && c != 'Σ')
  def coptic(c: Char): Boolean = c >= 'ϊ' && c <= 'ϻ'
  def letterlikeSymbols(c: Char): Boolean = c >= '℀' && c <= '⅏'
  def atomicIdentStart(c: Char): Boolean = letterlike(c) || (c == '_')
  def atomicIdentRest(c: Char): Boolean = atomicIdentStart(c) || (c >= '0' && c <= '9') || c == '\'' || c == 'ⁿ' || subscript(c)
  //noinspection DuplicatedCode
  def subscript(c: Char): Boolean = (c >= '₀' && c <= '₉') || (c >= 'ₐ' && c <= 'ₜ') || (c >= 'ᵢ' && c <= 'ᵪ')

  def sanitizeName(name: String): String =
    if (name.isEmpty)
      "x"
    else {
      // valid Lean identifiers: (https://leanprover.github.io/reference/lexical_structure.html#identifiers)
      val first = name.head
      val rest = name.tail

      val newFirst = if (atomicIdentStart(first)) first else '_'
      val newRest = rest.map(c => if (atomicIdentRest(c)) c else '_')

      s"$newFirst$newRest"
    }


  private def bigIntZero = BigInt(0)
  private def splitNameRegex = raw"(.*[^0-9])([0-9]*)".r

  private def findUnusedName(name: String): String = {
    val previous = assigned.putIfAbsent(name, BoxedUnit.UNIT)
    if (previous == null)
      name
    else {
      val (name1: String, index: BigInt) = name match {
        case `splitNameRegex`(name1, index) =>
          (name1, if (index.isEmpty) bigIntZero else BigInt(index))
        case _ => assert(false) // cannot happen unless name is empty or a number
      }

      @tailrec def find(i: BigInt): String = {
        val j = i + 1
        val name = name1 + j
        val previous = assigned.putIfAbsent(name, BoxedUnit.UNIT)
        if (previous == null)
          name
        else
          find(j)
      }
      find(index)
    }
  }

  def mapName(name: String | (String, Long),
              prefix: String = "",
              suggestion: String = "",
              category: Namespace): String =
    names.computeIfAbsent((category, name), { _ =>
      val rawName =
        if (suggestion.nonEmpty)
          suggestion
        else
          name match {
            case name: String => prefix + name
            case (name: String, index: Long) => prefix + name + index
          }

      val sanitizedName = sanitizeName(rawName)
      val mappedName = findUnusedName(sanitizedName)
      mappedName
    })
}
