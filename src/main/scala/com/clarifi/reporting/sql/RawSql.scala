package com.clarifi.reporting.sql

import math.Ordering
import scalaz._
import Scalaz._
import Equal._

/** The ultimate output of a SQL code generator. */
case class RawSql(private[RawSql] val contents: Vector[String]) {
  private[RawSql] lazy val stringValue = contents.mkString

  /** Produce the raw SQL, and any secondary data it may require. */
  def run: String = stringValue

  def isEmpty = contents.filter(_ != "").isEmpty
}

object RawSql {
  /** Produce a raw given some SQL. */
  implicit def raw(v: String) = RawSql(Vector(v))
  def raw[F[_]: Foldable](vs: F[String]) = RawSql(vs.foldLeft(Vector[String]())((a, b) => a :+ b))

  /** Raw is a monoid. */
  implicit val rawMonoid: Monoid[RawSql] = new Monoid[RawSql] {
    import std.vector._
    def append(left: RawSql, right: => RawSql) =
      RawSql(left.contents |+| right.contents)
    val zero = raw("")
  }

  final class RawStringJoins[F[_]](val value: F[RawSql]) {
    /** Like `mkString`, but for joining raws safely. */
    def rawMkString(join: String)(implicit ev: Foldable[F]) =
      value intercalate raw(join)
    /** Like `mkString`, but for joining raws safely. */
    def rawMkString(left: String, join: String, right: String
                   )(implicit ev: Foldable[F]) =
      raw(left) |+| (value intercalate raw(join)) |+| raw(right)
  }

  /** Raws can be interposed with strings. */
  implicit def rawStringJoins[F[_]](raws: F[RawSql]): RawStringJoins[F] =
    new RawStringJoins[F](raws)

  final class RawFormatter(val value: String) {
    /** Combine `raws` with a `formatSpec`.  The consequences of not
      * including enough directives to consume all `raws` are not
      * nice.
      */
    def formatRaws(raws: RawSql*) = raw(value format ((raws map (_.stringValue)): _*))
  }

  /** Raws can be laid out against format strings. */
  implicit def rawFormatter(s: String): RawFormatter = new RawFormatter(s)

  /** Raws can be ordered with respect to their literal,
    * unparameterized SQL content. */
  implicit val rawOrdering: Ordering[RawSql] = Ordering by (_.stringValue)
}
