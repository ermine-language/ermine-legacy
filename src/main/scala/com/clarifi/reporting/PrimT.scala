package com.clarifi.reporting

import java.util.{Date, UUID}

import scalaz.{@@, Equal, Ordering, Order, Semigroup, Show, Scalaz, Validation}
import scalaz.Tags.Disjunction
import scalaz.std.option._
import scalaz.syntax.bind._
import scalaz.syntax.show._
import Show._
import Equal._
import Order._
import Ordering._

abstract sealed class PrimT {
  type Value
  def isa(that: PrimT): Boolean
  def sup(that: PrimT): Option[PrimT]
  def nullable: Boolean
  def withNull: PrimT
  def name: String
  def primType: PrimType[_]
}

object PrimT {
  type Type = com.clarifi.reporting.PrimT
  type Union = Option[PrimT] @@ Disjunction

  private def nullify(nullable: Boolean, ty: PrimType[_]): PrimType[_] =
    if (nullable) PrimType primOption ty else ty

  case class ByteT(nullable: Boolean = false) extends PrimT {
    type Value = Byte
    def isa(that: PrimT) = that match {
      case ByteT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case ByteT(n) => Some(ByteT(nullable || n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Byte"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class ShortT(nullable: Boolean = false) extends PrimT {
    type Value = Short
    def isa(that: PrimT) = that match {
      case ShortT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case ShortT(n) => Some(ShortT(nullable || n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Short"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class IntT(nullable: Boolean = false) extends PrimT {
    type Value = Int
    def isa(that: PrimT) = that match {
      case IntT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case IntT(n) => Some(IntT(nullable || n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Int"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class LongT(nullable: Boolean = false) extends PrimT {
    type Value = Long
    def isa(that: PrimT) = that match {
      case LongT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case LongT(n) => Some(LongT(nullable || n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Long"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class StringT(len: Int, nullable: Boolean = false) extends PrimT {
    type Value = String
    def isa(that: PrimT) = that match {
      case StringT(l, n) => (len <= l) && (nullable <= n)
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case StringT(l, n) => Some(StringT(if (len == 0 || l == 0) 0
                                        else len max l, nullable || n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "String"
    def primType = nullify(nullable, PrimType primString len)
  }

  case class DateT(nullable: Boolean = false) extends PrimT {
    type Value = Date
    def isa(that: PrimT) = that match {
      case DateT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case DateT(n) => Some(DateT(nullable||n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Date"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class DoubleT(nullable: Boolean = false) extends PrimT {
    type Value = Double
    def isa(that: PrimT) = that match {
      case DoubleT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case DoubleT(n) => Some(DoubleT(nullable||n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Double"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class BooleanT(nullable: Boolean = false) extends PrimT {
    type Value = Boolean
    def isa(that: PrimT) = that match {
      case BooleanT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case BooleanT(n) => Some(BooleanT(nullable||n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "Bool"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  case class UuidT(nullable: Boolean = false) extends PrimT {
    type Value = UUID
    def isa(that: PrimT) = that match {
      case UuidT(n) => nullable <= n
      case _ => false
    }
    def sup(that: PrimT) = that match {
      case UuidT(n) => Some(UuidT(nullable||n))
      case _ => None
    }
    def withNull = this.copy(nullable = true)
    def name = "UUID"
    def primType = nullify(nullable, implicitly[PrimType[Value]])
  }

  def withName(s: String): PrimT = s match {
    case "Int"    => IntT  (false)
    case "Byte"   => ByteT (false)
    case "Short"  => ShortT(false)
    case "Long"   => LongT(false)
    case "String" => StringT(0, false)
    case "Date"   => DateT(false)
    case "Double" => DoubleT(false)
    case "Bool"   => BooleanT(false)
    case "UUID"   => UuidT(false)
  }

  def coerce(p:PrimT, s: String): Validation[Throwable, Any] = Validation.fromTryCatch(p match {
    case IntT(_)       => s.toInt
    case ByteT(_)      => s.toByte
    case ShortT(_)     => s.toShort
    case LongT(_)      => s.toLong
    case StringT(_, _) => s
    /**
     * TODO
     * Stephen would also strongly suggest, building from "Calendar getInstance ymdPivotTimeZone"
     * otherwise equality turns really dumb
     */
    case DateT(_)      => new java.text.SimpleDateFormat("YYYY/mm/dd").parse(s)
    case DoubleT(_)    => s.toDouble
    case BooleanT(_)   => s.toBoolean
    case UuidT(_)      => java.util.UUID.fromString(s)
  })

  implicit val PrimTEqual: Equal[PrimT] = equalA[PrimT]
  implicit val PrimTShow: Show[PrimT] = showA
  implicit val PrimTOrder: Order[PrimT] = implicitly[Order[String]].contramap(_.shows)

  /** `sup` forms a semigroup. */
  implicit val PrimTUnion: Semigroup[Union] = new Semigroup[Union] {
    def append(l: Union, r: => Union): Union =
      Disjunction(^(l, r)(_ sup _)(optionInstance).join)
  }

  def isNumeric(p:PrimT): Boolean = p match {
    case x: ByteT   => true
    case x: ShortT  => true
    case x: IntT    => true
    case x: LongT   => true
    case x: DoubleT => true
    case _ => false
  }

  def read(s: String): PrimT = {
    import ermine.Pos
    import ermine.parsing._
    val bool = (word("true") as true) | (word("false") as false)
    val strt : Parser[PrimT] = word("StringT") >> paren(for { n <- nat ; _ <- comma ; b <- bool } yield StringT(n.toInt, b))
    val nstr : Parser[Boolean => PrimT] =
      ("ByteT"    as ByteT)    |
      ("ShortT"   as ShortT)   |
      ("IntT"     as IntT)     |
      ("LongT"    as LongT)    |
      ("DoubleT"  as DoubleT)  |
      ("BooleanT" as BooleanT) |
      ("DateT"    as DateT)    |
      ("UuidT"    as UuidT)

    val main : Parser[PrimT] = strt | (for { c <- nstr ; b <- paren(bool) } yield c(b))

    // this is ugly
    main.run(ParseState(Pos("","",0,0,false), s, ""), Supply.create) match {
      case Right((_, x)) => x
      case _             => sys.error("Failed to read PrimT: \"" + s + "\"")
    }
  }
}
