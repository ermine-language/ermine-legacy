package com.clarifi.reporting

import scalaz._
import Scalaz._
import Show._
import Equal._
import Ordering._
import Order._

import java.util.{Date,Locale,UUID}

import java.text.{SimpleDateFormat,DateFormat,ParseException}

import PrimT._

/** Primitive relational expressions */
sealed abstract class PrimExpr(val typ: PrimT) extends Equals {
  type Value
  def value: Value
  def nullable: Boolean
  def isNull: Boolean = this match {
    case NullExpr(_) => true
    case _ => false
  }
  def valueOption: Option[Any] = this match {
    case NullExpr(pt) => None
    case _ => Some(value)
  }
  def extractNullableString(ifNull: => String): String = this match {
    case StringExpr(_, s) => s
    case DoubleExpr(_, d) => d.toString
    case ByteExpr(_, d) => d.toString
    case ShortExpr(_, d) => d.toString
    case LongExpr(_, d) => d.toString
    case IntExpr(_, i) => i.toString
    case DateExpr(_, d) => PrimExprs.dateFormatter.format(d)
    case BooleanExpr(_, b) => b.toString
    case UuidExpr(_, u) => u.toString
    case NullExpr(pt) => ifNull
  }

  def extractString: String = extractNullableString(sys.error("Could not extract a string value from null of type: " + typ))

  def extractDouble: Double = this match {
    case StringExpr(_, s) => s.toDouble
    case DoubleExpr(_, d) => d
    case ByteExpr(_, i) => i.toDouble
    case ShortExpr(_, i) => i.toDouble
    case IntExpr(_, i) => i.toDouble
    case LongExpr(_, i) => i.toDouble
    case DateExpr(_, d) => d.getTime.toDouble
    case _ => sys.error("Could not extract a double value from " + this)
  }

  def extractDate: Date = this match {
    case StringExpr(_, s) => DateFormat.getDateInstance.parse(s)
    case DoubleExpr(_, d) => new Date(d.toLong)
    case IntExpr(_, i) => new Date(i)
    case DateExpr(_, d) => d
    case _ => sys.error("Could not extract a date value from " + this)
  }

  def extractUuid: UUID = this match {
    case StringExpr(_, s) => UUID.fromString(s)
    case UuidExpr(_, s) => s
    case _ => sys.error("Could not extract a UUID value from " + this)
  }

  /** Minimally total catamorphism that preserves most value structure. */
  def minCata[Z](string: String => Z, double: Double => Z, bool: Boolean => Z,
                 date: Date => Z, uuid: UUID => Z, nul: => Z): Z = this match {
    case StringExpr(_, s) => string(s)
    case _: DoubleExpr | _: ByteExpr | _: ShortExpr | _: IntExpr
       | _: LongExpr => double(extractDouble)
    case DateExpr(_, d) => date(d)
    case BooleanExpr(_, b) => bool(b)
    case UuidExpr(_, u) => uuid(u)
    case NullExpr(_) => nul
  }

  def +(p: PrimExpr) = (this, p) match {
    case (DoubleExpr(b1, x), DoubleExpr(b2, y)) => DoubleExpr(b1 || b2, (x + y).toDouble)
    case (ByteExpr(b1, x), ByteExpr(b2, y)) => ByteExpr(b1 || b2, (x + y).toByte)
    case (ShortExpr(b1, x), ShortExpr(b2, y)) => ShortExpr(b1 || b2, (x + y).toShort)
    case (IntExpr(b1, x), IntExpr(b2, y)) => IntExpr(b1 || b2, x + y)
    case (LongExpr(b1, x), LongExpr(b2, y)) => LongExpr(b1 || b2, (x + y).toLong)
    case (DateExpr(b1, x), DateExpr(b2, y)) => DateExpr(b1 || b2, new Date((x.getTime + y.getTime).toLong))
    case (n@NullExpr(_), y) => n
    case (y, n@NullExpr(_)) => n
    case _ => sys.error(this.toString + " and " + p + " do not support addition.")
  }
  def -(p: PrimExpr) = (this, p) match {
    case (DoubleExpr(b1, x), DoubleExpr(b2, y)) => DoubleExpr(b1 || b2, (x - y).toDouble)
    case (ByteExpr(b1, x), ByteExpr(b2, y)) => ByteExpr(b1 || b2, (x - y).toByte)
    case (ShortExpr(b1, x), ShortExpr(b2, y)) => ShortExpr(b1 || b2, (x - y).toShort)
    case (IntExpr(b1, x), IntExpr(b2, y)) => IntExpr(b1 || b2, x - y)
    case (LongExpr(b1, x), LongExpr(b2, y)) => LongExpr(b1 || b2, x - y)
    case (DateExpr(b1, x), DateExpr(b2, y)) => DateExpr(b1 || b2, new Date(x.getTime - y.getTime))
    case (n@NullExpr(_), y) => n
    case (y, n@NullExpr(_)) => n
    case _ => sys.error(this.toString + " and " + p + " do not support subtraction.")
  }
  def *(p: PrimExpr) = (this, p) match {
    case (DoubleExpr(b1, x), DoubleExpr(b2, y)) => DoubleExpr(b1 || b2, x * y)
    case (ByteExpr(b1, x), ByteExpr(b2, y)) => ByteExpr(b1 || b2, (x * y).toByte)
    case (ShortExpr(b1, x), ShortExpr(b2, y)) => ShortExpr(b1 || b2, (x * y).toShort)
    case (IntExpr(b1, x), IntExpr(b2, y)) => IntExpr(b1 || b2, x * y)
    case (LongExpr(b1, x), LongExpr(b2, y)) => LongExpr(b1 || b2, x * y)
    case (DateExpr(b1, x), DateExpr(b2, y)) => DateExpr(b1 || b2, new Date(x.getTime * y.getTime))
    case (n@NullExpr(_), y) => n
    case (y, n@NullExpr(_)) => n
    case _ => sys.error(this.toString + " and " + p + " do not support multiplication.")
  }
  def /(p: PrimExpr) = (this, p) match {
    case (DoubleExpr(b1, x), DoubleExpr(b2, y)) => DoubleExpr(b1 || b2, x / y)
    case (ByteExpr(b1, x), ByteExpr(b2, y)) => ByteExpr(b1 || b2, (x / y).toByte)
    case (ShortExpr(b1, x), ShortExpr(b2, y)) => ShortExpr(b1 || b2, (x / y).toShort)
    case (IntExpr(b1, x), IntExpr(b2, y)) => IntExpr(b1 || b2, x / y)
    case (LongExpr(b1, x), LongExpr(b2, y)) => LongExpr(b1 || b2, x / y)
    case (n@NullExpr(_), y) => n
    case (y, n@NullExpr(_)) => n
    case _ => sys.error(this.toString + " and " + p + " do not support division.")
  }
  def pow(p: PrimExpr) = (this, p) match {
    case (DoubleExpr(b1, x), DoubleExpr(b2, y)) => DoubleExpr(b1 || b2, math.pow(x, y))
    case (ByteExpr(b1, x), ByteExpr(b2, y)) => ByteExpr(b1 || b2, math.pow(x, y).toByte)
    case (ShortExpr(b1, x), ShortExpr(b2, y)) => ShortExpr(b1 || b2, math.pow(x, y).toShort)
    case (IntExpr(b1, x), IntExpr(b2, y)) => IntExpr(b1 || b2, math.pow(x, y).toInt)
    case (LongExpr(b1, x), LongExpr(b2, y)) => LongExpr(b1 || b2, math.pow(x, y).toLong)
    case (DateExpr(b1, x), DateExpr(b2, y)) => DateExpr(b1 || b2, new Date(math.pow(x.getTime, y.getTime).toLong))
    case (n@NullExpr(_), y) => n
    case (y, n@NullExpr(_)) => n
    case _ => sys.error(this.toString + " and " + p + " do not support exponentiation.")
  }

  /** Change type to nullable, if not already. */
  def withNull: PrimExpr = if (this nullable) this else (this match {
    case x: UuidExpr => x.copy(nullable=true)
    case x: StringExpr => x.copy(nullable=true)
    case x: ByteExpr => x.copy(nullable=true)
    case x: ShortExpr => x.copy(nullable=true)
    case x: IntExpr => x.copy(nullable=true)
    case x: LongExpr => x.copy(nullable=true)
    case x: DoubleExpr => x.copy(nullable=true)
    case x: DateExpr => x.copy(nullable=true)
    case x: BooleanExpr => x.copy(nullable=true)
    case _: NullExpr => this
  })

  override def equals(a: Any): Boolean = a match {
    case a: PrimExpr => (a canEqual this) &&
      Order[PrimExpr].equal(this, a)
  }

  // NullExpr does not compare equal to itself in some contexts (evaluating predicates,
  // doing joins in Mem)
  def equalsIfNonNull(a: PrimExpr): Boolean =
    if (this.isNull || a.isNull) false
    else this == a

  override def toString: String = cata(Option(value))(_.toString, "")
}

case class UuidExpr(nullable: Boolean, value: UUID)
     extends PrimExpr(UuidT(nullable)) {
  type Value = UUID
}

case class StringExpr(nullable: Boolean, value: String)
     extends PrimExpr(StringT(0, nullable)) {
  type Value = String
}

case class ByteExpr(nullable: Boolean, value: Byte)
     extends PrimExpr(ByteT(nullable)) {
  type Value = Byte
}

case class ShortExpr(nullable: Boolean, value: Short)
     extends PrimExpr(ShortT(nullable)) {
  type Value = Short
}

case class IntExpr(nullable: Boolean, value: Int)
     extends PrimExpr(IntT(nullable)) {
  type Value = Int
}

case class LongExpr(nullable: Boolean, value: Long)
     extends PrimExpr(LongT(nullable)) {
  type Value = Long
}

case class DateExpr(nullable: Boolean, value: Date)
     extends PrimExpr(DateT(nullable)) {
  type Value = Date
}

case class BooleanExpr(nullable: Boolean, value: Boolean)
     extends PrimExpr(BooleanT(nullable)) {
  type Value = Boolean
}

case class NullExpr(t: PrimT) extends PrimExpr(t.withNull) {
  type Value = None.type
  override def equals(that: Any): Boolean = false
  override def hashCode: Int = 0
  def value = None
  def nullable = true
}

case class DoubleExpr(nullable: Boolean, value: Double)
     extends PrimExpr(PrimT.DoubleT(nullable)) { dbl =>
  type Value = Double
}

object PrimExprs {
  val dateFormatter = DateFormat.getDateInstance(DateFormat.SHORT, Locale.ENGLISH)
  val tz = java.util.TimeZone.getTimeZone("GMT")
  dateFormatter.getCalendar.setTimeZone(tz)

  val mmmyyyy = new SimpleDateFormat("MMM yyyy")
  val mmm = new SimpleDateFormat("MMM")
  val yyyy = new SimpleDateFormat("yyyy")

  def parseDate(s: String): Option[Date] =
    try { Some(dateFormatter.parse(s)) }
    catch { case e: ParseException => None }

  def formatDate(d: Date): String =
    dateFormatter.format(d)

  def formatMonthYear(d: Date): String =
    mmmyyyy.format(d)

  def formatYear(d: Date): String =
    yyyy.format(d)

  def formatMonth(d: Date): String =
    mmm.format(d)
}

object PrimExpr {
  implicit val PrimExprShow: Show[PrimExpr] = showFromToString[PrimExpr]

  private def ctorOrder(a: PrimExpr) = a match {
    case StringExpr(_, _)  => 0
    case DoubleExpr(_, _)  => 1
    case ByteExpr(_, _)    => 2
    case ShortExpr(_, _)   => 3
    case LongExpr(_, _)    => 4
    case IntExpr(_, _)     => 5
    case DateExpr(_, _)    => 6
    case BooleanExpr(_, _) => 7
    case UuidExpr(_, _)    => 8
    case NullExpr(_)       => 9
  }
  implicit val PrimExprOrder: Order[PrimExpr] = order((a, b) => {
    val typeorder = ctorOrder(a) ?|? ctorOrder(b)
    // XXX as of this comment scalaz Ordering semigroup is strict on
    // right, so we have to fake it
    if (typeorder === EQ)
    (a, b) match {
      case (StringExpr(_, v1), StringExpr(_, v2)) => v1 ?|? v2
      case (IntExpr(_, v1), IntExpr(_, v2)) => v1 ?|? v2
      // doubleOrdering doesn't follow the Order laws, so we can't use it.
      case (DoubleExpr(_, v1), DoubleExpr(_, v2)) => v1 ?|? v2
      case (ByteExpr(_, v1), ByteExpr(_, v2)) => v1 ?|? v2
      case (ShortExpr(_, v1), ShortExpr(_, v2)) => v1 ?|? v2
      case (LongExpr(_, v1), LongExpr(_, v2)) => v1 ?|? v2
      case (DateExpr(_, v1), DateExpr(_, v2)) => v1.getTime ?|? v2.getTime
      case (BooleanExpr(_, v1), BooleanExpr(_, v2)) => v1 ?|? v2
      case (UuidExpr(_, v1), UuidExpr(_, v2)) => v1 ?|? v2
      case (NullExpr(t1), NullExpr(t2)) => t1 ?|? t2
      case (a, b) => sys.error("Error in PrimExpr ordering: cannot compare " + a.shows + " with " + b.shows)
    }
    else typeorder
  })
  implicit val PrimOrdering = PrimExprOrder.toScalaOrdering

  def mkExpr(i: Int, t: PrimT) = t match {
    case StringT(l,n) => StringExpr(n, i.toString)
    case ByteT(n) => ByteExpr(n, i.toByte)
    case ShortT(n) => ShortExpr(n, i.toShort)
    case IntT(n) => IntExpr(n, i)
    case LongT(n) => LongExpr(n, i)
    case DoubleT(n) => DoubleExpr(n, i)
    case DateT(n) => DateExpr(n, new Date(i)) // Hack
    case BooleanT(n) => BooleanExpr(n, i != 0)
    case UuidT(n) => UuidExpr(n, new UUID(i, i)) // Hack
  }

  def mkExpr(d: Double, t: PrimT) = t match {
    case StringT(l,n) => StringExpr(n, d.toString)
    case ByteT(n) => ByteExpr(n, d.toByte)
    case ShortT(n) => ShortExpr(n, d.toShort)
    case IntT(n) => IntExpr(n, d.toInt)
    case LongT(n) => LongExpr(n, d.toLong)
    case DoubleT(n) => DoubleExpr(n, d)
    case DateT(n) => DateExpr(n, new Date(d.toLong)) // Hack
    case BooleanT(n) => BooleanExpr(n, d != 0.0)
    case UuidT(n) => UuidExpr(n, new UUID(d.toLong, d.toLong)) // Hack
  }

  def sumMonoid(t: PrimT) = new Monoid[PrimExpr] {
    val zero = mkExpr(0, t)
    def append(x: PrimExpr, y: => PrimExpr) = x + y
  }

  def minMonoid(t: PrimT) = new Monoid[PrimExpr] {
    val zero = NullExpr(t)
    def append(x: PrimExpr, y: => PrimExpr) = (x, y) match {
      case (StringExpr(n, a), StringExpr(m, b)) => StringExpr(m && n, if (a <= b) a else b)
      case (ByteExpr(n, a), ByteExpr(m, b)) => ByteExpr(m && n, a min b)
      case (ShortExpr(n, a), ShortExpr(m, b)) => ShortExpr(m && n, a min b)
      case (IntExpr(n, a), IntExpr(m, b)) => IntExpr(m && n, a min b)
      case (LongExpr(n, a), LongExpr(m, b)) => LongExpr(m && n, a min b)
      case (DoubleExpr(n, a), DoubleExpr(m, b)) => DoubleExpr(m && n, a min b)
      case (DateExpr(n, a), DateExpr(m, b)) => DateExpr(m && n, if (a before b) a else b)
      case (BooleanExpr(n, a), BooleanExpr(m, b)) => BooleanExpr(m && n, a && b)
      case (NullExpr(t), e) => e.withNull
      case (e, NullExpr(t)) => e.withNull
      case (_, _) => sys.error("Type mismatch: " + x.typ + " is not " + y.typ)
    }
  }

  def maxMonoid(t: PrimT) = new Monoid[PrimExpr] {
    val zero = NullExpr(t)
    def append(x: PrimExpr, y: => PrimExpr) = (x, y) match {
      case (StringExpr(n, a), StringExpr(m, b)) => StringExpr(m && n, if (a >= b) a else b)
      case (ByteExpr(n, a), ByteExpr(m, b)) => ByteExpr(m && n, a max b)
      case (ShortExpr(n, a), ShortExpr(m, b)) => ShortExpr(m && n, a max b)
      case (IntExpr(n, a), IntExpr(m, b)) => IntExpr(m && n, a max b)
      case (LongExpr(n, a), LongExpr(m, b)) => LongExpr(m && n, a max b)
      case (DoubleExpr(n, a), DoubleExpr(m, b)) => DoubleExpr(m && n, a max b)
      case (DateExpr(n, a), DateExpr(m, b)) => DateExpr(m && n, if (a after b) a else b)
      case (BooleanExpr(n, a), BooleanExpr(m, b)) => BooleanExpr(m && n, a || b)
      case (NullExpr(t), e) => e.withNull
      case (e, NullExpr(t)) => e.withNull
      case (_, _) => sys.error("Type mismatch: " + x.typ + " is not " + y.typ)
    }
  }

}
