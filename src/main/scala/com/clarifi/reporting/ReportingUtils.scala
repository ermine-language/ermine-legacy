package com.clarifi.reporting

import scalaz._
import Scalaz._
import Ordering._
import syntax.traverse._
import scalaz.Scalaz._

import com.clarifi.reporting.Predicate._
import com.clarifi.reporting.Reporting._

/**
 * Collection of various utility and convenience methods that do not
 * have a good home.
 *
 * @author smb
 */
object ReportingUtils {
  /**
    * Simplifies a nested Predicate into something less nested; for
    * example it converts Not(Or(false, true)) -> false.
    *
    * @param p Predicate to simplify.
    * @param truth Guaranteed true about `p`'s domain.
    * @param falsehood Guaranteed false about `p`'s domain.
    * @note simplifyPredicate(p, t, f).eval(m) = p.eval(m)
    *       if `t`, `f` are sound.
    * @note Do not try `simplifyPredicate(p, Predicates constancies p)`.
    *       That just ties knots.
    */
  def simplifyPredicate(p: Predicate,
                        truth: Reflexivity[ColumnName] = Reflexivity.zero,
                        falsehood: Reflexivity[ColumnName] = Reflexivity.zero
                       ): Predicate = {
    import Predicate._
    lazy val simplEnv = truth.consts collect {
      case (k, Some(v)) => k -> Op.OpLiteral(v)
    }
    def rec(p: Predicate): Predicate = p match {
      case Lt(l, r) =>
        Lt(l simplify simplEnv, r simplify simplEnv)
      case Gt(l, r) =>
        Gt(l simplify simplEnv, r simplify simplEnv)
      case Eq(l, r) => (l simplify simplEnv, r simplify simplEnv) match {
        case (l, r) if l === r => Atom(true)
        case (Op.ColumnValue(l, _), Op.ColumnValue(r, _))
            if truth equivalent Set(l, r) => Atom(true)
        case (Op.ColumnValue(l, _), Op.ColumnValue(r, _))
            if falsehood equivalent Set(l, r) => Atom(false)
        case (l, r) => Eq(l, r)
      }
      case Not(p) => rec(p) match {
        case Atom(b) => Atom(!b)
        case Not(p2) => p2
        case p2 => Not(p2)
      }
      case Or(a, b) => (rec(a), rec(b)) match {
        case (Atom(true), _) => Atom(true)
        case (_, Atom(true)) => Atom(true)
        case (Atom(false), b2) => b2
        case (a2, Atom(false)) => a2
        case (a2, b2) => Or(a2, b2)
      }
      case And(a, b) => (rec(a), rec(b)) match {
        case (Atom(false), _) => Atom(false)
        case (_, Atom(false)) => Atom(false)
        case (Atom(true), b2) => b2
        case (a2, Atom(true)) => a2
        case (a2, b2) => And(a2, b2)
      }
      case _ => p
    }
    rec(p)
  }

  /**
   * Builds a predicate from a header. If there is more than one header, the
   * other function, g, determines how to combine predicates.
   */
  def buildPredicate[A](l: List[A], f: A => Predicate, g: (Predicate, Predicate) => Predicate): Predicate = l match {
    case h :: Nil => f(h)
    case h :: t => g(f(h), buildPredicate(t, f, g))
    case _ => sys.error("Cannot build predicate for unexpected empty header.")
  }

  /** Partition contiguous sequences of `xs` values with equal `kf`
    * results. */
  def splitWith[A, B: Equal](xs: Seq[A])(kf: A => B) = {
    def rec(xs: Seq[A]): Seq[Seq[A]] = xs match {
      case Seq() => Seq()
      case _ =>
        val k = kf(xs.head)
        xs.tail span (e => k === kf(e)) fold
          ((sp, br) => (xs.head +: sp) +: rec(br))
    }
    rec(xs)
  }

  /** The entirely safe reduction of `xs`. */
  def foldNel[X](xs: NonEmptyList[X])(f: (X, X) => X) =
    xs.tail.fold(xs.head)(f)

  /** Reduce with log₂n append depth. */
  def binaryReduce[X](xs: Iterable[X])(f: (X, X) => X): Option[X] =
    if (xs isEmpty) None else {
      @annotation.tailrec
      def pass(xs: Stream[X]): X = xs match {
        case Stream(x) => x
        case xs => pass(xs grouped 2 map {case Seq(a, b) => f(a, b)
                                          case Seq(a) => a} toStream)
      }
      Some(pass(xs toStream))
    }

  object MapElts {
    /** Destructure a map.  Only really works with zero or one element
      * maps. */
    def unapplySeq[K, V](m: Map[K, V]) = Some(m.toSeq)
  }

  /**
   * Various methods to repeat a blank space some number of times and
   * optionally add additional items after that.
   */
  def padding(level: Int): Cord = List.fill(level)(" ").mkString("")
  def paddingRel(level: Int): Cord = padding(level) |+| "Relation(\n"
  def paddingVar(level: Int): Cord = padding(level) |+| "Variable("

  def prettyOp(o: Op, level: Int): Cord = {
    import com.clarifi.reporting.Op._
    padding(level) |+| implicitly[Show[Op]].show(o)
  }

  def prettyPredicate(p: Predicate, level: Int): Cord = {
    def binop(lbl: String, s1: Op, s2: Op): Cord =
      padding(level) |+| lbl |+| "(\n" |+|
      prettyOp(s1, level + 2) |+|
      padding(level + 2) |+| ",\n" |+|
      prettyOp(s2, level + 2) |+|
      padding(level) |+| ")\n"
    p match {
      case Atom(b) => padding(level) |+| "Atom(" |+| b.show |+| ")\n"
      case Lt(s1, s2) => binop("Lt", s1, s2)
      case Gt(s1, s2) => binop("Gt", s1, s2)
      case Eq(s1, s2) => binop("Eq", s1, s2)
      case Not(p) => {
        padding(level) |+| "Not(\n" |+|
        prettyPredicate(p, level + 2) |+|
        padding(level) |+| ")\n"
      }
      case Or(p1, p2) => {
        padding(level) |+| "Or(\n" |+|
        prettyPredicate(p1, level + 2) |+|
        padding(level + 2) |+| ",\n" |+|
        prettyPredicate(p2, level + 2) |+|
        padding(level) |+| ")\n"
      }
      case And(p1, p2) => {
        padding(level) |+| "And(\n" |+|
        prettyPredicate(p1, level + 2) |+|
        padding(level + 2) |+| ",\n" |+|
        prettyPredicate(p2, level + 2) |+|
        padding(level) |+| ")\n"
      }
      case _ => sys.error("Predicate unsupported: " + p)
    }
  }

  def prettyRelationHeader(h: Header, level: Int): Cord = {
    import com.clarifi.reporting.PrimT

    def printHeader(l: List[(String, PrimT.Type)], level: Int): Cord = {
      l match {
        case (c, t) :: Nil => {
          padding(level) |+| implicitly[Show[String]].show(c) |+|
            " -> " |+| implicitly[Show[PrimT.Type]].show(t) |+| "\n"
        }
        case (c, t) :: tail => {
          padding(level) |+| implicitly[Show[String]].show(c) |+|
            " -> " |+| implicitly[Show[PrimT.Type]].show(t) |+| ",\n" |+|
          printHeader(tail, level)
        }
        case _ => padding(level)
      }
    }

    padding(level) |+| "Map(\n" |+|
    printHeader(h.toList, level + 2) |+|
    padding(level) |+| "),\n"
  }
}
