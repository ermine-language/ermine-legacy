package com.clarifi.reporting.ermine.core

import com.clarifi.reporting.ermine.Monadic

sealed abstract class Gen[+A] extends Monadic[Gen,A] with Traversable[A] {
  def self = this
  implicit def lift[B](v: Gen[B]) = v
  def flatMap[B](f: A => Gen[B]): Gen[B]
  def map[B](f: A => B): Gen[B]
  def when(b: Boolean): Gen[Unit] = if (b) skip else Unbound(())
  def fold[B](bd: Int => B, unbd: A => B): B
  def foreach[U](f: A => U): Unit
}

case class Bound(i: Int) extends Gen[Nothing] {
  def flatMap[B](f: Nothing => Gen[B]) = this
  def map[B](f: Nothing => B) = this
  def fold[B](bd: Int => B, unbd: Nothing => B) = bd(i)
  def foreach[U](f: Nothing => U) {}
}

case class Unbound[+A](a: A) extends Gen[A] {
  def flatMap[B](f: A => Gen[B]) = f(a)
  def map[B](f: A => B) = Unbound(f(a))
  def fold[B](bd: Int => B, unbd: A => B) = unbd(a)
  def foreach[U](f: A => U) { f(a) }
}

