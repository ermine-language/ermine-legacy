package com.clarifi.reporting.ermine.session.foreign

import collection.immutable.{Vector => Vec}
import math.{Ordering => O}

object Vector {
  def empty[A]: Vector[A] = Vec.empty
  def isEmpty[A](v: Vec[A]): Boolean = v.isEmpty
  def snoc[A](a: A, v: Vec[A]): Vec[A] = v :+ a
  def cons[A](a: A, v: Vec[A]): Vec[A] = a +: v
  def at[A](i: Int, v: Vec[A]): A = v(i)
  def append[A](v: Vec[A], v2: Vec[A]): Vec[A] = v ++ v2
  def reverse[A](v: Vec[A]): Vec[A] = v.reverse
  def take[A](n: Int, v: Vec[A]): Vec[A] = v take n
  def drop[A](n: Int, v: Vec[A]): Vec[A] = v drop n
  def sort[A](lt: (A,A) => Boolean, v: Vec[A]): Vec[A] =
    v.sorted(O.fromLessThan(lt))
  def map[A,B](f: A => B, v: Vec[A]): Vec[B] = v map f
  def filter[A](f: A => Boolean, v: Vec[A]): Vec[A] = v filter f
  def find[A](f: A => Boolean, v: Vec[A]): Option[A] = v.find(f)
  def concatMap[A,B](f: A => Vec[B], v: Vec[A]): Vec[B] = v flatMap f
  def fold[A](z: A, f: (A,A) => A, v: Vec[A]): A = v.fold(z)(f)
  def zipWith[A,B,C](f: (A,B) => C, v: Vec[A], v2: Vec[B]): Vec[C] = v zip v2 map f.tupled
}
