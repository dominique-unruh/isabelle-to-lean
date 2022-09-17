import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.Proofterm.PThm
import de.unruh.isabelle.pure.{Abs, App, Bound, ConcreteTerm, Const, Context, Cterm, Free, MLValueTerm, Proofterm, TFree, TVar, Term, Thm, Typ, Type, Var}

import java.io.{FileOutputStream, PrintWriter}
import java.nio.file.Path
import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.ExecutionContext.Implicits.global

sealed trait LogicalEntity

//noinspection UnstableApiUsage
case class Theorem(pthm: PThm) extends LogicalEntity {
  override def toString: String = s"Theorem(${pthm.header.name}@${pthm.header.serial})"
  val fullName: String = Main.quote(name = pthm.header.name, category = "theorem")
}

case class Axiom(name: String, prop: Term) extends LogicalEntity {
  override def toString: String = s"Axiom($name)"
  val fullName: String = Main.quote(prefix = "axiom_", name = name, category = "axiom")
  def print(output: PrintWriter): Unit = {
    output.println(s"Axiom $fullName : ${Main.translateTerm(prop)}")
    output.println()
  }
}

case class Constant(name: String) extends LogicalEntity {
  override def toString: String = s"Const($name)"
  val fullName: String = Main.quote(name = name, category = "constant")
}

//noinspection UnstableApiUsage
object Main {
  val setup: Isabelle.Setup = Isabelle.Setup(isabelleHome = Path.of("c:/Programs/Isabelle2021-1"), logic = "HOL-Proofs")
  implicit val isabelle: Isabelle = new Isabelle(setup)
  val ctxt: Context = Context("Main")

  def getPThm(thm: Thm): PThm = {
    @tailrec
    def strip(prf: Proofterm) : PThm = prf match {
      case Proofterm.AppP(proof1, _) => strip(proof1)
      case Proofterm.Appt(proof, _) => strip(proof)
      case prf : Proofterm.PThm => prf
    }
    strip(thm.proofOf)
  }

  type Serial = Long

  val output = new PrintWriter(new FileOutputStream("test.txt"))

  object axioms {
    def count: Int = nameMap.size

    private val nameMap = mutable.HashMap[String, Axiom]()

    def compute(name: String, prop: Term): Axiom = nameMap.get(name) match {
      case Some(axiom) =>
        assert(prop == axiom.prop)
        axiom
      case None =>
        val axiom = actuallyCompute(name, prop)
        nameMap.put(name, axiom)
        axiom
    }

    private def actuallyCompute(name: String, prop: Term): Axiom = {
      println(s"Computing axiom: $name: ${prop.pretty(ctxt)}")
      val axiom = Axiom(name = name, prop = prop)
      axiom.print(output)
      axiom
    }
  }

  object constants {
    def count: Int = nameMap.size

    private val nameMap = mutable.HashMap[String, Constant]()

    def compute(name: String): Constant = nameMap.get(name) match {
      case Some(constant) => constant
      case None =>
        val constant = actuallyCompute(name)
        nameMap.put(name, constant)
        constant
    }

    private def actuallyCompute(name: String): Constant = {
      println(s"Computing constant: $name: $name")
      val constant = Constant(name)
      constant
    }
  }

  object theorems {
    def count: Int = serialMap.size
    def namedCount: Int = nameMap.size

    private val serialMap = mutable.HashMap[Serial, Theorem]()
    private val nameMap = mutable.HashMap[String, Serial]()
    def compute(pthm: PThm) : Theorem = serialMap.get(pthm.header.serial) match {
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
              println(s"*** Theorem ${pthm.header.name} already encountered ***")
              println(s"  $old: ${oldProp.pretty(ctxt)}")
              println(s"  ${pthm.header.serial}: ${prop.pretty(ctxt)}")
              if (prop != oldProp)
                println("  Propositions differ!")
            case None =>
              nameMap.put(pthm.header.name, pthm.header.serial) match {
                case Some(old) =>
                case None =>
              }
          }
        }
        theorem
    }
  }

  def proofToString(proof: Proofterm): String = proof match {
    case Proofterm.MinProof => "_"
    case Proofterm.AppP(proof1, proof2) => s"AppP(${proofToString(proof1)},${proofToString(proof2)})"
    case Proofterm.Appt(proof, term) => s"Appt(${proofToString(proof)}, ${term.map(_.pretty(ctxt))}"
    case Proofterm.AbsP(name, term, proof) => s"AbsP($name, ${term.map(_.pretty(ctxt))}, ${proofToString(proof)}"
    case Proofterm.Abst(name, typ, proof) => s"Abst($name, ${typ.map(_.pretty(ctxt))}, ${proofToString(proof)}"
    case Proofterm.Hyp(term) => s"Hyp(${term.pretty(ctxt)}"
    case Proofterm.PAxm(name, prop, typ) =>
      val axiom = axioms.compute(name, prop)
      s"$axiom(${typ.map(_.map(_.pretty(ctxt)))})"
    case Proofterm.PBound(index) => s"PBound($index)"
    case Proofterm.OfClass(typ, clazz) => s"OfClass(${typ.pretty(ctxt)}, $clazz)"
    case Proofterm.Oracle(name, term, typ) => s"Oracle($name, ${term.pretty(ctxt)}, ${typ.map(_.map(_.pretty(ctxt)))}"
    case pthm : PThm =>
      val theorem = theorems.compute(pthm)
      theorem.toString
  }

  def actuallyCompute(pthm: Proofterm.PThm): Theorem = {
    println(s"Computing: ${pthm.header.name}@${pthm.header.serial}")
    println(s"  Proposition: ${pthm.header.prop.pretty(ctxt)}")
    val proof = pthm.fullProof(ctxt.theoryOf)
    println(s"  Proof: ${proofToString(proof)}")
    Theorem(pthm=pthm)
  }

  def main(args: Array[String]): Unit = {
    val thmName = "HOL.conjI"

    val thm = Thm(ctxt, thmName)
    val pthm = getPThm(thm)
    val prf = pthm.body.proofOpenMlValue.retrieveNow
    theorems.compute(pthm)

    println(s"# theorems:       ${theorems.count}")
    println(s"# named theorems: ${theorems.namedCount}")
    println(s"# axioms:         ${axioms.count}")

    output.close()
  }

  // TODO: check for duplicate Var/Free with different types
  def translateTerm(term: Term, env: List[String] = Nil): String = term match {
    case App(t,u) => s"(${translateTerm(t, env)}) (${translateTerm(u, env)})"
    case Abs(name,typ,term) =>
      val name2 = quote(name, category = "abs")
      s"fn ($name2 : ${translateTyp(typ)}) => ${translateTerm(term, name2 :: env)}"
    case Bound(i) => env(i)
    case Var(name,index,typ) => quote(s"_$name$index", category = "var")
    case Free(name,typ) => name
    case Const(name, typ) =>
      val const = constants.compute(name)
      s"${const.fullName} : ${translateTyp(typ)}"
  }

  // TODO: check for duplicate TFree/TVar with different types
  def translateTyp(typ: Typ) : String = typ match {
    case Type(tcon,typs @_*) => (tcon :: typs.toList.map("("+translateTyp(_)+")")).mkString(" ")
    case TVar(name, index, sort) => s"_$name$index"
    case TFree(name, sort) => name
  }

  // TODO avoid conflicts between categories
  def quote(name: String, prefix: String = "", category: String): String =
    prefix + name.replace(".","_")
}
