package com.clarifi.reporting.ermine

import Document._
import scalaz.{ Order, Ordering }
import scalaz.Scalaz._

/** a Loc is an abstract possibly built-in location
  *
  * @author EAK
  */

sealed abstract class Loc extends Located {
  def loc = this
  def orElse(l: Loc): Loc
  def unifiedWith(l: Loc): Loc = orElse(l)
  def inferred: Loc = this // inferred from something at this location, not at this location
  def instantiatedBy(l: Loc): Loc = orElse(l) // instantated from an Annot or a Forall at l
  def checked: Loc = this // implied by checking the current location
  def generalized: Loc = this
}

object Loc {
  implicit def relocatableLoc: Relocatable[Loc] = new Relocatable[Loc] {
    def setLoc(old: Loc, loc: Loc) = loc
  }
  object builtin extends Loc {
    override def report(msg: Document, rest: Document*) = vsep(msg :: rest.toList)
    def orElse(l: Loc) = l
    override def toString = "-"
    override def msg(s: String) = s + " (builtin)"
  }
  def locOrder: Order[Loc] = Order.order((a, b) => (a, b) match {
    case (`builtin`, `builtin`) => Ordering.EQ
    case (`builtin`, _) => Ordering.LT
    case (_, `builtin`) => Ordering.GT
    case (a: Pos, b: Pos) => a ?|? b
    case (Inferred(a), Inferred(b)) => a ?|? b
    case (a: Pos, Inferred(b)) => (a ?|? b) |+| Ordering.LT
    case (Inferred(a), b: Pos) => (a ?|? b) |+| Ordering.GT
  })
}

case class Inferred(p: Pos) extends Loc {
  override def report(msg: Document, rest: Document*): Document = p.report(msg :+: "inferred from", rest :_*)
  override def toString = "inferred from " + p.toString
  override def orElse(l : Loc) = l match {
    case p : Pos => p
    case _       => this
  }
}

/** A Pos is a location that actually occurs in a source file. */
case class Pos(fileName: String, current: String, line: Int, column: Int, ending: Boolean) extends Loc {
  /** new Pos("foo.e", contents) -- will construct a position that points to the start of a file with the given contents */
  def bump(c: Char, i: String, o: Int) =
    if   (c == '\n') {
      val ix = i.indexOf('\n', o)
      if (ix == -1) Pos(fileName, i substring o, line + 1, 1, true)
      else Pos(fileName, i.substring(o, ix), line + 1, 1, false)
    }
    else if (c == '\t') Pos(fileName, current, line, column + (8 - column % 8), ending)
    else Pos(fileName, current, line, column + 1, ending)

  override def report(msg: Document, rest: Document*): Document = vsep(
    (fileName :: ":" :: line.toString :: ":" :: column.toString :: ":" :+: msg) ::
    (current :: text(if (ending) "<EOF>" else "")) ::
    ((" " * (column - 1)) :: text("^")) ::
    rest.toList
  )

  override def inferred: Loc = Inferred(this)

  override def toString = fileName + "(" + line + ":" + column + ")" // report("position").toString
  override def hashCode = (fileName, line, column).hashCode
  override def equals(a: Any) = a match {
    case Pos(ofileName, _, oline, ocolumn, oending) => fileName == ofileName && line == oline && column == ocolumn && ending == oending
    case _ => false
  }
  override def msg(s: String): String = s + " at " + fileName + ":" + line + ":" + column
  def orElse(l: Loc) = this
}

object Pos {
  def start(fileName: String, contents: String) = {
    val current = contents.takeWhile(_ != '\n')
    Pos(fileName, current, 1, 1, current.length == contents.length)
  }
  implicit def posOrder: Order[Pos] = new Order[Pos] {
    def order(p: Pos, q: Pos): Ordering = (p.fileName ?|? q.fileName) |+| (p.line ?|? q.line) |+| (p.column ?|? q.column)
  }
}


/** Located types know how to transform errors to give better location information */

trait Located {
  def loc: Loc
  def report(msg: Document, rest: Document*): Document = loc.report(msg, rest:_*)
  def die(msg: Document, rest: Document*): Nothing = throw Death(loc.report(msg, rest:_*))
  def error(msg: Document, rest: Document*): Nothing = sys.error(loc.report(msg, rest:_*).toString)
  def msg(s: String): String = loc.msg(s)
}

/** A relocatable instance for a Locatable type knows how to change its current location */
abstract class Relocatable[T <: Located] {
  def setLoc(t: T, loc: Loc): T
}

object Relocatable {
  def preserveLoc[A <: Located, B<:Located:Relocatable](sub: Map[A,B]): PartialFunction[A,B] = {
    case x if sub.contains(x) => setLoc(sub(x),x.loc)
  }
}

