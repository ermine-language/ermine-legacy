package com.clarifi.reporting.ermine.session.foreign

import scalaz.{Tree => T}

object Tree {
  def leaf[A](a: A): T[A] = T.leaf(a)
  def node[A](a: A, cs: Stream[T[A]]): T[A] = T.node(a, cs.toStream)
  def map[A,B](f: A => B, t: T[A]): T[B] = t map f
  def flatten[A](t: T[A]): Stream[A] = t.flatten
  def scan[A,B](f: (A, Stream[B]) => B, t: T[A]): T[B] =
    t.scanr((a: A, bs: Stream[T[B]]) => f(a, bs map (_.rootLabel)))
  def zipWith[A,B,C](f: (A,B) => C, a: T[A], b: T[B]): T[C] =
    node(f(a.rootLabel, b.rootLabel), a.subForest.zip(b.subForest).map { case (l,r) => zipWith(f, l, r) })
}
