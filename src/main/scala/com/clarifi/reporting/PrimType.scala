package com.clarifi.reporting

import java.util.Date
import java.util.UUID

import Reporting._
import com.clarifi.reporting.PrimT._

import scalaz._
import Scalaz._

/**
 * Represents a primitive value in both the scala and relational type
 * systems by wrapping the primitive scala value and providing ways to
 * wrap or unwrap the value in both type systems.
 *
 * Various implicit PrimTypes are provided to seamlessly convert
 * valued to/from the scala and relational type systems.
 */
case class PrimType[A](
  val typ: PrimT,
  val expr: A => PrimExpr,  // expr(a).typ.sup(nullTyp).isDefined == true must hold
  val unExpr: PrimExpr => A // expr -| unExpr with isomorphism where possible
) {
  def nullTyp: PrimT = typ.withNull
}

/**
 * Contains implicit conversions of scala values from scala types to
 * primitive relational types.
 */
object PrimType {

  // magic constant for the length of a reference field.
  // TODO: move this somewhere else?
  def refLen = 80

  implicit val primRefID : PrimType[RefID] = PrimType[RefID](StringT(refLen), StringExpr(false, _), {
    case StringExpr(_,s) => RefID(s)
    case e => sys.error("Not a RefID: " + e.shows)
  })

  implicit val primBoolean : PrimType[Boolean] = PrimType[Boolean](BooleanT(), BooleanExpr(false, _), {
    case BooleanExpr(_,b) => b
    case e => sys.error("Not a Boolean expression: " + e.shows)
  })

  def primString(len: Int) : PrimType[String] = PrimType[String](StringT(len), StringExpr(false, _), {
    case StringExpr(_,s) => s
    case e => sys.error("Not a String expression: " + e.shows)
  })

  implicit val primByte : PrimType[Byte] = PrimType[Byte](ByteT(), ByteExpr(false, _), {
    case ByteExpr(_,i) => i
    case e => sys.error("Not a Byte expression: " + e.shows)
  })

  implicit val primShort : PrimType[Short] = PrimType[Short](ShortT(), ShortExpr(false, _), {
    case ShortExpr(_,i) => i
    case e => sys.error("Not a Short expression: " + e.shows)
  })

  implicit val primInt : PrimType[Int] = PrimType[Int](IntT(), IntExpr(false, _), {
    case IntExpr(_,i) => i
    case e => sys.error("Not an Int expression: " + e.shows)
  })

  implicit val primLong : PrimType[Long] = PrimType[Long](LongT(), LongExpr(false, _), {
    case LongExpr(_,l) => l
    case e => sys.error("Not a Long expression: " + e.shows)
  })

  implicit val primDouble : PrimType[Double] = PrimType[Double](DoubleT(), DoubleExpr(false, _), {
    case DoubleExpr(_,d) => d
    case e => sys.error("Not a Double expression: " + e.shows)
  })

  implicit val primDate : PrimType[Date] = PrimType[Date](DateT(), x => DateExpr(false, x), {
    case DateExpr(_,t) => t
    case e => sys.error("Not a Date expression: " + e.shows)
  })

  implicit val primUuid : PrimType[UUID] = PrimType[UUID](UuidT(), x => UuidExpr(false, x), {
    case UuidExpr(_,u) => u
    case e => sys.error("Not a Uuid expression: " + e.shows)
  })

  // this should ideally only be instantiated for Option[T] for some SimplePrimType[T]
  // but this implicit is more convenient to work with.
  implicit def primOption[T](implicit T: PrimType[T]) = PrimType[Option[T]](T.nullTyp, {
    case Some(e) => T.expr(e)
    case None    => NullExpr(T.nullTyp)
  }, {
    case NullExpr(_) => None
    case e           => Some(T.unExpr(e))
  })

  /**
   * Converts a primitive scala value of some type to the corresponding
   * expression in the relational type system.
   */
  implicit def toPrim[A](a: A)(implicit t: PrimType[A]): PrimExpr = t.expr(a)

  /**
   * Converts a primitive relational expression of some type to the
   * corresponding value in the scala type system.
   */
  def fromPrim[A](a: PrimExpr {type Value <: A}
                )(implicit t: PrimType[A]): A = t.unExpr(a)
}
