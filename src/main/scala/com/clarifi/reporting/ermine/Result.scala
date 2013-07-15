package com.clarifi.reporting.ermine

sealed abstract class Result[+S,+A] extends Functorial[({type F[+X] = Result[S,X]})#F,A] {
  def self = this
}

case class Success[+S,+A](body: A, state : S) extends Result[S,A] {
  def map[B](f: A => B) = Success(f(body), state)
}

case class Failure(error: Option[Document], stack: List[String]) extends Result[Nothing,Nothing] {
  def map[B](f: Nothing => B) = this
  override def as[B](b: => B) = this
}
