package com.clarifi.reporting
package relational

import scalaz._
import Scalaz._
import scalaz.Show._
import scalaz.Equal._

import util.{Clique, Keyed, PartitionedSet}
import Reporting._

sealed abstract class Relation[+M,+R] {
  def bimap[N,S](f: M => N, g: R => S): Relation[N, S]
  def map[S](f: R => S): Relation[M, S] = bimap(x => x, f)
  def mapMem[N](f: M => N): Relation[N, R] = bimap(f, x => x)

  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]): Relation[N, S]
  def flatMap[N >: M, S](f: R => Relation[N, S]): Relation[N, S] = subst(VarM(_), f)
  def flatMem[N, S >: R](f: M => Mem[S, N]): Relation[N, S] = subst(f, VarR(_))

  def foreach(f: M => Any, g: R => Any): Unit

  def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                              g: Object => Option[Mem[S, N]]): Relation[N, S]
  def unquoteR[S >: R, N >: M](f: Object => Option[Relation[N, S]]): Relation[N, S] = unquote(f, x => None)
  def unquoteM[S >: R, N >: M](f: Object => Option[Mem[S, N]]): Relation[N, S] = unquote(x => None, f)
}

case class VarR[+R](v: R) extends Relation[Nothing, R] {
  def bimap[N, S](f: Nothing => N, g: R => S) = VarR(g(v))
  def subst[N, S](f: Nothing => Mem[S,N], g: R => Relation[N,S]) = g(v)
  def foreach(f: Nothing => Any, g: R => Any) = g(v)
  override def unquote[S >: R, N >: Nothing](f: Object => Option[Relation[N, S]],
                                             g: Object => Option[Mem[S, N]]): Relation[N, S] = this
}

case class Limit[+M,+R](
  r: Relation[M,R],
  start: Option[Int],
  end: Option[Int],
  order: List[(String, SortOrder)]
) extends Relation[M,R] {
  def bimap[N, S](f: M => N, g: R => S) = Limit(r.bimap(f, g), start, end, order)
  def subst[N, S](f: M => Mem[S,N], g: R => Relation[N, S]) = Limit(r.subst(f, g), start, end, order)
  def foreach(f: M => Any, g: R => Any) = r.foreach(f, g)
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Limit(r.unquote(f, g), start, end, order)
}

/**
 * Intermediate form between Relation and SQL. Provided for (re)writing queries that translate to
 * nicer-looking and faster SQL.
 */
case class SelectR[+M,+R](
  rs: List[Relation[M,R]],
  cs: Map[Attribute, Op],
  where: Predicate
) extends Relation[M,R] {
  def bimap[N, S](f: M => N, g: R => S) = SelectR(rs map (_.bimap(f, g)), cs, where)
  def subst[N, S](f: M => Mem[S,N], g: R => Relation[N, S]) = SelectR(rs map (_.subst(f, g)), cs, where)
  def foreach(f: M => Any, g: R => Any) = rs foreach (_.foreach(f, g))
  override def equals(other: Any) = other match {
    case SelectR(rs2, cs2, where2) =>
      rs.toSet == rs2.toSet && cs == cs2 && where == where2
    case _ => false
  }
  override def hashCode: Int = (rs.toSet, cs, where).hashCode
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    SelectR(rs.map(_.unquote(f, g)), cs, where)
}

case class MemoR[+M,+R](r: Relation[M,R]) extends Relation[M,R] {
  def bimap[N, S](f: M => N, g : R => S) = MemoR(r.bimap(f,g))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = MemoR(r.subst(f,g))
  def foreach(f: M => Any, g: R => Any) = r.foreach(f,g)
  override def equals(other: Any) = other match {
    case MemoR(r2) => r == r2
    case _ => false
  }
  override def hashCode: Int = (r, 1).hashCode
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    MemoR(r.unquote(f, g))
}

case class LetR[+M,+R](r: Ext[M,R], expr: Relation[M,RLevel[M, R]]) extends Relation[M,R] {
  def bimap[N, S](f: M => N, g: R => S) = LetR(r.bimap(f, g), expr.bimap(f, (_.bimap(f, g))))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) =
    LetR(r subst (f, g), expr subst (v => f(v).mapRel(x => RPop(VarR(x))), l => VarR(l subst (f, g))))
  def foreach(f: M => Any, g: R => Any) = { r.foreach(f, g) ; expr.foreach(f, (_.foreach(f, g))) }
  override def equals(other: Any) = other match {
     case LetR(r2, e2) => r == r2 && Relation.fromScope(expr) == Relation.fromScope(e2)
     case _ => false
  }
  override def hashCode: Int = (r, Relation.fromScope(expr)).hashCode
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    LetR(r.unquote(g, f),
         expr.unquote(x => f(x).map(v => VarR(RPop(v))), x => g(x).map(_.mapRel(v => RPop(VarR(v))))))
}

case class Join[+M, +R](fst: Relation[M, R], snd: Relation[M, R]) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Join(fst bimap (f, g), snd bimap (f, g))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Join(fst subst (f, g), snd subst (f, g))
  def foreach(f: M => Any, g: R => Any) { fst foreach (f, g) ; snd foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Join(fst.unquote(f, g), snd.unquote(f, g))
}

case class JoinOn[+M, +R](fst: Relation[M, R], snd: Relation[M, R], cs: Set[(String, String)]) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = JoinOn(fst bimap (f, g), snd bimap (f, g), cs)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = JoinOn(fst subst (f, g), snd subst (f, g), cs)
  def foreach(f: M => Any, g: R => Any) { fst foreach (f, g) ; snd foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    JoinOn(fst.unquote(f, g), snd.unquote(f, g), cs)
}

case class Union[+M, +R](fst: Relation[M, R], snd: Relation[M, R]) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Union(fst bimap (f, g), snd bimap (f, g))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Union(fst subst (f, g), snd subst (f, g))
  def foreach(f: M => Any, g: R => Any) { fst foreach (f, g) ; snd foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Union(fst.unquote(f, g), snd.unquote(f, g))
}

case class Minus[+M, +R](fst: Relation[M, R], snd: Relation[M, R]) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Minus(fst bimap (f, g), snd bimap (f, g))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Minus(fst subst (f, g), snd subst (f, g))
  def foreach(f: M => Any, g: R => Any) { fst foreach (f, g) ; snd foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Minus(fst.unquote(f, g), snd.unquote(f, g))
}

case class Filter[+M, +R](rel: Relation[M, R], p: Predicate) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Filter(rel bimap (f, g), p)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Filter(rel subst (f, g), p)
  def foreach(f: M => Any, g: R => Any) { rel foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Filter(rel.unquote(f, g), p)
}

case class Project[+M, +R](rel: Relation[M, R], cs: Map[Attribute, Op]) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Project(rel bimap (f, g), cs)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Project(rel subst (f, g), cs)
  def foreach(f: M => Any, g: R => Any) { rel foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Project(rel.unquote(f, g), cs)
}

/** Except gets optimized away in the Optimizer */
case class Except[+M, +R](rel: Relation[M, R], cs: Set[ColumnName]) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Except(rel bimap (f, g), cs)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Except(rel subst (f, g), cs)
  def foreach(f: M => Any, g: R => Any) { rel foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Except(rel.unquote(f, g), cs)
}

/** Combine gets optimized away in the Optimizer */
case class Combine[+M, +R](rel: Relation[M, R], attr: Attribute, op: Op) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Combine(rel bimap (f, g), attr, op)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Combine(rel subst (f, g), attr, op)
  def foreach(f: M => Any, g: R => Any) { rel foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Combine(rel.unquote(f, g), attr, op)
}

case class Aggregate[+M, +R](rel: Relation[M, R], attr: Attribute, agg: AggFunc) extends Relation[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = Aggregate(rel bimap (f, g), attr, agg)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = Aggregate(rel subst (f, g), attr, agg)
  def foreach(f: M => Any, g: R => Any) { rel foreach (f, g) }
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                       g: Object => Option[Mem[S, N]]): Relation[N, S] =
    Aggregate(rel.unquote(f, g), attr, agg)
}

sealed abstract class HardRel extends Relation[Nothing, Nothing] {
  def bimap[N, S](f: Nothing => N, g: Nothing => S) = this
  def subst[N, S](f: Nothing => Mem[S, N], g: Nothing => Relation[N, S]) = this
  def foreach(f: Nothing => Any, g: Nothing => Any) = ()
  def header: Header
  override def unquote[S >: Nothing, N >: Nothing](f: Object => Option[Relation[N, S]],
                                                   g: Object => Option[Mem[S, N]]): Relation[N, S] = this
}

/** A table-valued stored procedure.
  *
  * @param headerOrder SQL uses order, rather than column name, in
  *   exciting bug-causing ways.  Normally, we resolve potential
  *   conflicts between orders by applying a universal sorting
  *   strategy—i.e., the Ord[String] sort.  The nature of the sort is
  *   irrelevant; all that matters is consistency.  We can't control
  *   the ordering of procedure calls in the same way, though, so we
  *   have to save it, and use it when we're ready to pull the call
  *   result into our world.
  */
case class TableProc[+M, +R](args: List[(String, Relation[M, R]) \/ PrimExpr],
                             headerOrder: OrderedHeader,
                             fun: String, namespace: List[String])
     extends Relation[M, R] {
  import TableProc.relFunctor
  def bimap[N, S](f: M => N, g: R => S) =
    copy(args = relFunctor.map(args)(_ bimap (f, g)))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) =
    copy(args = relFunctor.map(args)(_ subst (f, g)))
  def foreach(f: M => Any, g: R => Any) =
    args foreach (_.swap foreach (_._2 foreach (f, g)))
  override def unquote[S >: R, N >: M](f: Object => Option[Relation[N, S]],
                                     g: Object => Option[Mem[S, N]]): Relation[N, S] =
    copy(args = relFunctor.map(args)(_ unquote (f, g)))

  def header: Header = headerOrder.toMap
}
object TableProc {
  private type RArg[+A] = A \/ PrimExpr
  private type LTup[+A] = (String, A)
  val argFunctor = Functor[List].compose[RArg](Bifunctor[\/].leftFunctor)
  val argFoldable = Foldable[List].compose[RArg](Bifoldable[\/].leftFoldable)
  val relFunctor = argFunctor compose Functor[LTup]
  val relFoldable = argFoldable compose Foldable[LTup]
}

case class Table(header: Header, n: TableName) extends HardRel
case class RelEmpty(header: Header) extends HardRel
// Tiny literals turn into filters in the optimizer
case class SmallLit(tups: NonEmptyList[Record]) extends HardRel {
  val header = recordHeader(tups.head)
}
case class QuoteR(n: Object) extends HardRel {
  def header = sys.error("Panic: Asked for the header of a quote.")
  override def unquote[R, M](f: Object => Option[Relation[M, R]],
                             g: Object => Option[Mem[R, M]]): Relation[M, R] =
    f(n) getOrElse this
}

sealed abstract class RLevel[+M, +R] {
  def bimap[N, S](f: M => N, g: R => S): RLevel[N, S]
  def map[S](f: R => S): RLevel[M, S] = bimap(x => x, f)
  def mapMem[N](f: M => N): RLevel[N, R] = bimap(f, x => x)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]): RLevel[N, S]
  def flatMap[S,N >: M](f: R => Relation[N, S]): RLevel[N, S] = subst(VarM(_), f)
  def flatMapMem[S >: R, N](f: M => Mem[S, N]): RLevel[N, S] = subst(f, VarR(_))
  def foreach(f: M => Any, g: R => Any): Unit
}

case object RTop extends RLevel[Nothing, Nothing] {
  def bimap[N, S](f: Nothing => N, g: Nothing => S) = this
  def subst[N, S](f: Nothing => Mem[S, N], g: Nothing => Relation[N, S]) = this
  def foreach(f: Nothing => Any, g: Nothing => Any) = ()
}

case class RPop[+M, +R](e: Relation[M,R]) extends RLevel[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = RPop(e bimap (f, g))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = RPop(e subst (f, g))
  def foreach(f: M => Any, g: R => Any) = e foreach (f, g)
}

object Relation {
  type RScope[+M, +R] = Relation[M, RLevel[M, R]]

  def abstrakt[M, R](p: R => Boolean, r: Relation[M, R]): RScope[M, R] = r.map(v => if(p(v)) RTop else RPop(VarR(v)))

  def instantiate[M, R](x: => Relation[M, R], s: RScope[M, R]): Relation[M, R] = s flatMap {
    case RTop    => x
    case RPop(v) => v
  }

  implicit def relTraversable[M, R](r: Relation[M,R]): Traversable[R] =
    new Traversable[R] { def foreach[U](f: R => U) { r foreach (x => (), f) } }

  def toScope[M, R](mem: Relation[M, Option[R]]): RScope[M, R] = mem map {
    case None => RTop
    case Some(e) => RPop(VarR(e))
  }

  def fromScope[R, M](rel: RScope[M, R]): Relation[M, Option[R]] = rel flatMap {
    case RTop => VarR(None)
    case RPop(e) => e map (Some(_))
  }

  implicit def relEq[M: Equal, R: Equal]: Equal[Relation[M, R]] = equalA

}

object RLevel {
  implicit def rLevelEq[M: Equal, R: Equal]: Equal[RLevel[M, R]] = new Equal[RLevel[M, R]] {
    def equal(r1: RLevel[M, R], r2: RLevel[M, R]) = (r1, r2) match {
      case (RTop, RTop) => true
      case (RPop(v1), RPop(v2)) => v1 === v2
      case _ => false
    }
  }
}

object RenameR {
  def apply[M, R](r: Relation[M, R], n1: Attribute, n2: ColumnName): Relation[M, R] =
    Except(Combine(r, Attribute(n2, n1.t), Op.ColumnValue(n1.name, n1.t)), Set(n1.name))
}

