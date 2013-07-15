package com.clarifi.reporting

import com.clarifi.machines._

import scala.collection.SeqLike

import backends._

import scalaz._
import scalaz.syntax.foldable._
import scalaz.syntax.order._
import scalaz.std.option._
import scalaz.std.list._
import scalaz.std.vector._

package object relational {
  import SortOrder._

  def sorting(inorder: List[(String, SortOrder)], outorder: List[(String, SortOrder)]): Process[Record, Record] = {
    val (pre, post) = ((inorder.map(some).toStream ++ Stream.continually(none)) zip outorder
                       span { case (x, y) => x == some(y) })
    val chunkCols = pre collect {case (Some((s, _)), _) => s} toSet
    val sortCols = (post map (_._2) toList)
    if (sortCols.isEmpty) Process.apply(i => i)
    else
      Process.grouping(
        (t1: Record, t2: Record) => (t1 filterKeys chunkCols) == (t2 filterKeys chunkCols)).
        outmap(sort(_, sortCols)) andThen Machine.flattened((x: Vector[Record] => Any) => x)
  }

  case class Closed[F[_, _]](out: F[Nothing, Nothing], header: Header) {
    def map[G[_, _]](f: F[Nothing, Nothing] => G[Nothing, Nothing]): Closed[G] =
      Closed[G](f(out), header)
  }

  type ClosedExt = Closed[Ext]
  type ClosedRel = Closed[Relation]
  type ClosedMem = Closed[Mem]

  implicit def memClosedMem(mem: Mem[Nothing, Nothing]) = Typer.closedMem(mem)

  implicit def relClosedRel(rel: Relation[Nothing, Nothing]) = Typer.closedRel(rel)

  implicit def extClosedExt(ext: Ext[Nothing, Nothing]) = Typer.closedExt(ext)

  /** Ordering on records that have all columns in `ord`. */
  def recordOrd(ord: List[(String, SortOrder)]): Order[Record] =
    Order.order((x, y) => ord.foldMap{
      case (n, Asc) => x(n) ?|? y(n)
      case (n, Desc) => y(n) ?|? x(n)
    })

  def sort[R](ts: SeqLike[Record, R], order: List[(String, SortOrder)]): R =
    ts sorted recordOrd(order).toScalaOrdering

  type OrderedProcedure[M[+_], +A] = List[(String, SortOrder)] => M[Procedure[scalaz.Id.Id, A]]
}
