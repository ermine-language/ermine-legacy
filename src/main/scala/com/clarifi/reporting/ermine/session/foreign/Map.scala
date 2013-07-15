package com.clarifi.reporting.ermine.session.foreign

import scala.collection.immutable.{SortedMap => SM}
import scala.math.{Ordering => SOrder}

import scalaz.syntax.std.function2._
import scalaz.syntax.std.tuple._

/** Simplified SortedMap methods/functions for invocation from
  * Ermine. */
object SortedMap {
  /** Foreign data representation of Ermine maps. */
  type FD[K, +V] = SM[K, V]

  def map[K, A, B](fa: FD[K, A])(f: A => B): FD[K, B] = {
    import fa.ordering
    // XXX can we walk the FD to avoid ordering?
    fa map {case (k, v) => (k, f(v))}
  }

  private[this] def partitionBy[A, K](xs: Vector[A])(f: A => K)
                                     (implicit o: SOrder[K]): Stream[Vector[A]] =
    if (xs isEmpty) Stream.empty
    else xs span (x => o equiv (f(xs.head), f(x))) fold (_ #:: partitionBy(_)(f))

  def groupBy[A, K](xs: Vector[A])(f: A => K)(implicit o: SOrder[K]
                   ): FD[K, Vector[A]] =
    SM(partitionBy(xs map (a => (f(a), a)) sortBy (_._1))(_._1)
       map (xs => (xs.head._1, xs map (_._2))):_*)

  def unionWith[K, A](l: FD[K, A], r: FD[K, A])(b: (A, A) => A): FD[K, A] = {
    // Try to do fewer comparisons, while preserving call order of `b`.
    val (sm, big, f) = if (l.size < r.size) (l, r, b) else (r, l, b.flip)
    big ++ sm.map {case (smk, smv) =>
        (smk, if (big isDefinedAt smk) f(smv, big(smk))
              else smv)
    }
  }
}
