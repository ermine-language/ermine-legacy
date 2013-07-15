package com.clarifi.reporting
package relational

import com.clarifi.reporting.{ SortOrder }
import com.clarifi.reporting.Reporting._

import com.clarifi.machines._

import scalaz._
import Scalaz._

abstract class Scanner[G[_]](implicit G: Monad[G], Dist : Distributive[G]) { self =>

  /** Scan a relation r, iterating over its records by f in the order specified.
    * The order is given by a list of pairs where the first element specifies
    * the column name and the second element specifies the order.
    */
  def scanRel[A: Monoid](r: Relation[Nothing, Nothing],
                         f: Process[Record, A],
                         order: List[(String, SortOrder)] = List()): G[A]

  def scanMem[A: Monoid](r: Mem[Nothing, Nothing],
                         f: Process[Record, A],
                         order: List[(String, SortOrder)] = List()): G[A]

  def scanExt[A: Monoid](r: Ext[Nothing, Nothing],
                         f: Process[Record, A],
                         order: List[(String, SortOrder)] = List()): G[A]

  def collect(r: Ext[Nothing, Nothing]): G[Vector[Record]] =
    scanExt(r, Process.wrapping[Record], List())

  val M = G
  val D = Dist
}
