package com.clarifi.reporting
package relational

import scalaz._
import Scalaz._

/** Multi-sourced relations */
sealed abstract class Ext[+M,+R] {
  def bimap[N, S](f: M => N, g: R => S): Ext[N, S]
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]): Ext[N, S]
  def foreach(f: M => Any, g: R => Any): Unit
  def unquote[N >: M, S >: R](f: Object => Option[Mem[S, N]], g: Object => Option[Relation[N, S]]): Ext[N, S] = this
  def unquoteR[N >: M, S >: R](g: Object => Option[Relation[N, S]]): Ext[N, S] = unquote(_ => None, g)
  def unquoteM[N >: M, S >: R](f: Object => Option[Mem[S, N]]): Ext[N, S] = unquote(f, _ => None)
}

/** Memory-based source */
case class ExtMem[+M, +R](mem: Mem[R, M]) extends Ext[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = ExtMem(mem bimap (g, f))
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = ExtMem(mem subst (g, f))
  def foreach(f: M => Any, g: R => Any) = mem foreach (g, f)
  override def unquote[N >: M, S >: R](f: Object => Option[Mem[S, N]], g: Object => Option[Relation[N, S]]): Ext[N, S] =
    ExtMem(mem.unquote(f, g))
}

/** External relational source */
case class ExtRel[+M, +R](rel: Relation[M, R], database: String) extends Ext[M, R] {
  def bimap[N, S](f: M => N, g: R => S) = ExtRel(rel bimap (f, g), database)
  def subst[N, S](f: M => Mem[S, N], g: R => Relation[N, S]) = ExtRel(rel subst(f, g), database)
  def foreach(f: M => Any, g: R => Any) = rel foreach (f, g)
  override def unquote[N >: M, S >: R](f: Object => Option[Mem[S, N]],
                                       g: Object => Option[Relation[N, S]]): Ext[N, S] =
    ExtRel(rel.unquote(g, f), database)
}

object Ext {
  implicit def extEq[M: Equal, R: Equal]: Equal[Ext[M, R]] = new Equal[Ext[M, R]] {
    def equal(e1: Ext[M, R], e2: Ext[M, R]) = (e1, e2) match {
      case (ExtMem(m1), ExtMem(m2)) => m1 === m2
      case (ExtRel(r1, db1), ExtRel(r2, db2)) => r1 === r2 && db1 === db2
      case _ => false
    }
  }
}

object AggregateE {
  def apply[M, R](r: Ext[M, R], attr: Attribute, agg: AggFunc): Ext[M, R] = r match {
    case ExtRel(e, db) => ExtRel(Aggregate(e, attr, agg), db)
    case ExtMem(e) => ExtMem(AggregateM(e, attr, agg))
    case e => ExtMem(AggregateM(EmbedMem(e), attr, agg))
  }
}

object ProjectE {
  def apply[M, R](r: Ext[M, R], cols: Map[Attribute, Op]): Ext[M, R] = r match {
    case ExtRel(e, db) => ExtRel(Project(e, cols), db)
    case ExtMem(e) => ExtMem(ProjectM(e, cols))
    case e => ExtMem(ProjectM(EmbedMem(e), cols))
  }
}

object CombineE {
  def apply[M, R](r: Ext[M, R], attr: Attribute, op: Op): Ext[M, R] = r match {
    case ExtRel(e, db) => ExtRel(Combine(e, attr, op), db)
    case ExtMem(e) => ExtMem(CombineM(e, attr, op))
    case e => ExtMem(CombineM(EmbedMem(e), attr, op))
  }
}

object ExceptE {
  def apply[M, R](r: Ext[M, R], cols: Set[ColumnName]): Ext[M, R] = r match {
    case ExtRel(e, db) => ExtRel(Except(e, cols), db)
    case ExtMem(e) => ExtMem(ExceptM(e, cols))
    case e => ExtMem(ExceptM(EmbedMem(e), cols))
  }
}

object RenameE {
  def apply[M, R](r: Ext[M, R], attr: Attribute, col: ColumnName): Ext[M, R] = r match {
    case ExtRel(e, db) => ExtRel(RenameR(e, attr, col), db)
    case ExtMem(e) => ExtMem(RenameM(e, attr, col))
    case e => ExtMem(RenameM(EmbedMem(e), attr, col))
  }
}

/** Convenience constructor for a common case. If r1 and r2 are different things,
    then this does nothing sane. */
object JoinE {
  def apply[M, R](r1: Ext[M, R], r2: Ext[M, R]): Ext[M, R] = (r1, r2) match {
    case (ExtRel(e1, db1), ExtRel(e2, db2)) =>
      if (true) ExtRel(Join(e1, e2), db1) else ExtRel(LetR(ExtRel(e1, db1), Join(VarR(RTop), VarR(RPop(e2)))), db2)
    case (ExtMem(e1), ExtMem(e2)) => ExtMem(HashInnerJoin(e1, e2))
    case (ExtRel(e1, db), ExtMem(e2)) => ExtRel(LetR(ExtMem(e2), Join(VarR(RPop(e1)), VarR(RTop))), db)
    case (ExtMem(e1), ExtRel(e2, db)) => ExtRel(LetR(ExtMem(e1), Join(VarR(RTop), VarR(RPop(e2)))), db)
  }
}

object FilterE {
  def apply[M, R](r: Ext[M, R], p: Predicate): Ext[M, R] = r match {
    case ExtRel(e, db) => ExtRel(Filter(e, p), db)
    case ExtMem(e) => ExtMem(FilterM(e, p))
    case e => ExtMem(FilterM(EmbedMem(e), p))
  }
}

object MemoE {
  def apply[M, R](r: Ext[M, R]) : Ext[M, R] = r match {
    case ExtRel(e,db) => ExtRel(MemoR(e), db)
    case e => e
  }
}
