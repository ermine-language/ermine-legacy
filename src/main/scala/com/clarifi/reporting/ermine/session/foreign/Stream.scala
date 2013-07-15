package com.clarifi.reporting.ermine.session.foreign

import scala.{Stream => S}

object Stream {
  def empty[A]: S[A] = S.empty
  def cons[A](h: A, t: () => S[A]): S[A] = h #:: t()
  def map[A,B](f: A => B, s: Stream[A]): Stream[B] = s map f
  def flatMap[A,B](f: A => Stream[B], s: Stream[A]): Stream[B] = s flatMap f
  def isEmpty[A](s: Stream[A]): Boolean = s.isEmpty
  def toList[A](s: Stream[A]): List[A] = s.toList
  def filter[A](f: A => Boolean, s: Stream[A]): Stream[A] = s filter f
  def take[A](n: Int, s: Stream[A]): Stream[A] = s take n
  def drop[A](n: Int, s: Stream[A]): Stream[A] = s drop n
  def length[A](s: Stream[A]): Int = s length
  def zipWith[A,B,C](f: (A,B) => C, s: Stream[A], s2: Stream[B]): Stream[C] =
    s zip s2 map f.tupled
  def append[A](s: Stream[A], s2: () => Stream[A]): Stream[A] = s append s2()
}
