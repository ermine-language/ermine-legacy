package com.clarifi

import scalaz.Cofree

import scalaz._
import Scalaz._
import scalaz.Show._
import scalaz.Equal._
import scalaz.Order._

import java.math.BigInteger

package object reporting {
  /** Relational algebra. */
  type Projection = Map[Attribute, Op]

  /** Special uses only; most should sort Headers. */
  type OrderedHeader = List[(ColumnName, PrimT)]

  type Header = Map[ColumnName, PrimT]

  import java.util.UUID._
  def guid = randomUUID.toString.replaceAll("-", "")

  def sguid = new BigInteger(randomUUID.toString.replaceAll("-", ""), 16).toString(36)

  def headerProj(h: Header): Projection =
    h map { case (n, t) => Attribute(n, t) -> Op.ColumnValue(n, t) }

  def sup(h1: Header, h2: Header): Option[Header] =
    if (h1.keySet != h2.keySet) None
    else h1.keySet.toList.map(k => (h1(k) sup h2(k)).map((k,_))).sequence.map(_.toMap)

  val emptyHeader: Header = Map()

  type ColumnName = String

  type Record = Map[ColumnName, PrimExpr]

  /** Force all the implicit threading here, so Ermine can get at it to
    * sort tuples, and we have an easy way to talk about it.
    *
    * @todo SMRC Optimize for common l.keySet == r.keySet case?
    */
  val RecordOrder: Order[Record] = implicitly
  //   implicitly[Order[IndexedSeq[(ColumnName, PrimExpr)]]].contramap((r:Record) =>
  //    r.toIndexedSeq.sortBy((p: (ColumnName, PrimExpr)) => p._1))

  def recordHeader(t: Record): Header = t map { case (k, v) => k -> v.typ }

  type TypeError = List[String]

  type TypeTag = ValidationNel[String, Header]

  type SourceWith[A] = (Set[Source], A)
  type Sourced = SourceWith[TypeTag]

  import IterV._
  implicit val StreamEnumerator = new Enumerator[Stream] {
    @annotation.tailrec
    def apply[E, A](e: Stream[E], i: IterV[E, A]): IterV[E, A] = e match {
      case Stream() => i
      case x #:: xs => i match {
        case Done(_,_) => i
        case Cont(k) => apply(xs, k(El(x)))
      }
    }
  }

  /**
   * Converts a TypeTag to a Header.
   */
  def typeTagToHeader(t: TypeTag): Header = t.fold(e => sys.error(e.list.mkString("\n")), s => s)
}
