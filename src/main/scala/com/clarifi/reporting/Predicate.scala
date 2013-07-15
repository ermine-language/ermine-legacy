package com.clarifi.reporting

import scalaz._
import Scalaz._
import Equal._
import Show._

/** A condition evaluated in the context of a relational record. */
sealed abstract class Predicate extends TraversableColumns[Predicate] {
  import Predicate._

  /** Fold. */
  def apply[z](atom: (Boolean) => z,
               lt: (Op, Op) => z,
               gt: (Op, Op) => z,
               eq: (Op, Op) => z,
               not: (z) => z,
               or: (z, z) => z,
               and: (z, z) => z,
               isNull: Op => z): z = {
    def rec(p: => Predicate): z = p match {
      case Atom(truth) => atom(truth)
      case Lt(left, right) => lt(left, right)
      case Gt(left, right) => gt(left, right)
      case Eq(left, right) => eq(left, right)
      case Not(p) => not(rec(p))
      case Or(left, right) => or(rec(left), rec(right))
      case And(left, right) => and(rec(left), rec(right))
      case IsNull(op) => isNull(op)
    }
    rec(this)
  }

  /** Evaluate; for symmetry. */
  def eval = Predicates toFn this

  /** Lift a nonrecursive Op transformation into this predicate. */
  def liftOp[F[_]: Applicative](f: Op => F[Op]): F[Predicate] = {
    def binop(b: (Op, Op) => Predicate)(l: Op, r: Op) =
      ^(f(l), f(r))(b)
    apply[F[Predicate]](
      atom = lit => (Atom(lit): Predicate).pure[F],
      lt = binop(Lt),
      gt = binop(Gt),
      eq = binop(Eq),
      not = (_ map Not),
      or = (l, r) => ^(l, r)(Or),
      and = (l, r) => ^(l, r)(And),
      isNull = (o => f(o) map (IsNull)))
  }

  def traverseColumns[F[_]: Applicative](f: ColumnName => F[ColumnName]): F[Predicate] =
    liftOp(_.traverseColumns(f))

  def typedColumnFoldMap[Z: Monoid](f: (ColumnName, PrimT) => Z): Z =
    liftOp[({type λ[α] = Z})#λ](_ typedColumnFoldMap f)

  /** Lift `Op#postReplace(f)` into this predicate.  Despite its
    * similarity, this is not the same operation as `liftOp`
    * itself. */
  def postReplaceOp[F[_]: Monad](f: Op => F[Op]): F[Predicate] =
    liftOp(_.postReplace(f))
}

object Predicate {
  case class Atom(truth: Boolean) extends Predicate
  case class Lt(left: Op, right: Op) extends Predicate
  case class Gt(left: Op, right: Op) extends Predicate
  case class Eq(left: Op, right: Op) extends Predicate
  case class Not(p: Predicate) extends Predicate
  case class Or(left: Predicate, right: Predicate) extends Predicate
  case class And(left: Predicate, right: Predicate) extends Predicate
  case class IsNull(expr: Op) extends Predicate // sql fail

  implicit val PredicateEqual: Equal[Predicate] = equalA
  implicit val PredicateShow: Show[Predicate] = showFromToString

  /** A predicate that requires the subject be a superset of `tup`. */
  def fromRecord(tup: Record): Predicate = Predicates all (tup map {
    case (cn, cv) => Eq(Op.ColumnValue(cn, cv.typ), Op.OpLiteral(cv))
  })
}

