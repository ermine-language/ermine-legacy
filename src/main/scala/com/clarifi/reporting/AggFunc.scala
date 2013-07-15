package com.clarifi.reporting

import scalaz._
import Scalaz._
import Equal._
import Show._

import com.clarifi.machines._
import com.clarifi.machines.Source._

sealed abstract class AggFunc extends TraversableColumns[AggFunc] {
  import AggFunc._

  def traverseColumns[F[+_]: Applicative](f: ColumnName => F[ColumnName]): F[AggFunc] =
    this match {
      case Count => Count.pure[F]
      case Sum(op) => op.traverseColumns(f).map(Sum(_))
      case Avg(op) => op.traverseColumns(f).map(Avg(_))
      case Min(op) => op.traverseColumns(f).map(Min(_))
      case Max(op) => op.traverseColumns(f).map(Max(_))
      case Stddev(op) => op.traverseColumns(f).map(Stddev(_))
      case Variance(op) => op.traverseColumns(f).map(Variance(_))
    }

  def typedColumnFoldMap[Z: Monoid](f: (ColumnName, PrimT) => Z): Z =
    this match {
      case Count => mzero[Z]
      case Sum(op) => op typedColumnFoldMap f
      case Avg(op) => op typedColumnFoldMap f
      case Min(op) => op typedColumnFoldMap f
      case Max(op) => op typedColumnFoldMap f
      case Stddev(op) => op typedColumnFoldMap f
      case Variance(op) => op typedColumnFoldMap f
    }

  /** Fold. */
  def apply[z](count:  => z, sum: (Op) => z, avg: (Op) => z,
               min: (Op) => z, max: (Op) => z,
               stddev: (Op) => z, variance: (Op) => z): z = this match {
    case Count => count
    case Sum(op) => sum(op)
    case Avg(op) => avg(op)
    case Min(op) => min(op)
    case Max(op) => max(op)
    case Stddev(op) => stddev(op)
    case Variance(op) => variance(op)
  }
}

object AggFunc {
  case object Count extends AggFunc
  case class Sum(op: Op) extends AggFunc
  case class Avg(op: Op) extends AggFunc
  case class Min(op: Op) extends AggFunc
  case class Max(op: Op) extends AggFunc
  case class Stddev(op: Op) extends AggFunc
  case class Variance(op: Op) extends AggFunc

  implicit val AggFuncEqual: Equal[AggFunc] = equalA
  implicit val AggFuncShow: Show[AggFunc] = showFromToString

  import PrimT._
  import PrimExpr._
  import java.util.{Date, UUID}

  import IterV._
  import Reducer._
  import Op._

  def reduce[F[_]](a: AggFunc, t: PrimT)(implicit F: Foldable[F]): F[Record] => PrimExpr =
    xs => (reduceProcess(a, t) cap source(xs)).foldRight(NullExpr(t):PrimExpr)((a, _) => a)

  def count(t: PrimT): Process[Record, PrimExpr] =
    reducer(unitReducer((_: Record) => 1)).outmap(mkExpr(_, t))

  def sum(f: Op, m: Monoid[PrimExpr]): Process[Record, PrimExpr] =
    reducer(unitReducer(f.eval(_:Record))(m))

  def avg(f: Op, t: PrimT): Process[Record, PrimExpr] = {
    implicit val m = sumMonoid(t)
    reducer(unitReducer((tup: Record) => (f.eval(tup), 1))).outmap(x => x._1 / mkExpr(x._2, t))
  }

  def variance(f: Op, t: PrimT): Process[Record, PrimExpr] = {
    implicit val m = sumMonoid(t)
    reducer(unitReducer((e: Record) => {
      val x = f.eval(e)
      (x, x * x) : (PrimExpr, PrimExpr)
    })).outmap {
      case (ms, m) => ms - m * m
    }
  }

  def stddev(f: Op, t: PrimT): Process[Record, PrimExpr] =
    variance(f, t).outmap(x => mkExpr(math.sqrt(x.extractDouble), t))

   /** A `Process` that reduces with a monoid. */
  def reducer[A, B](r: Reducer[A, B]): Process[A, B] = {
    def go(acc: B): Process[A, B] =
      Plan.await[A].orElse(Plan.emit(acc) >> Stop).flatMap(a => go(r.snoc(acc, a)))
    go(r.zero)
  }

  def reduceProcess(a: AggFunc, t: PrimT): Process[Record, PrimExpr] =
    a match {
      case Count => count(t)
      case Sum(f) => sum(f, sumMonoid(t))
      case Avg(f) => avg(f, t)
      case Min(f) => sum(f, minMonoid(t))
      case Max(f) => sum(f, maxMonoid(t))
      case Stddev(f) => stddev(f, t)
      case Variance(f) => variance(f, t)
    }
}

