package com.clarifi.reporting.ermine

import java.io.Writer
import java.io.StringWriter
import scalaz._
import scalaz.Scalaz._

abstract class DocException(msg: String, val doc: Document) extends Exception(msg)

case object DocNil extends Document
case object DocNewline extends Document
case class DocBreak(hard:Boolean = true) extends Document
class DocText(val txt: String) extends Document
object DocText{
  def apply(txt:String):DocText = new DocText(if(txt == null) "(null)" else txt)
  def unapply(d: DocText) : Option[String] = Some(d.txt)
}
case class DocGroup(doc: Document) extends Document
case class DocNest(indent: Int, doc: Document) extends Document
case class DocCons(hd: Document, tl: Document) extends Document
case class DocColumn(f: Int => Document) extends Document
case class DocNesting(f: Int => Document) extends Document
// case class DocUnion(f: Document, g: Document) extends Document


abstract class Document {
  import Document._

  def ::(hd: Document): Document = DocCons(hd, this)
  def ::(hd: String): Document = DocCons(DocText(hd), this)
  def :/:(hd: Document): Document = hd :: DocBreak(true) :: this
  def :/:(hd: String): Document   = hd :: DocBreak(true) :: this
  def :/+:(hd: Document): Document = hd :: DocGroup(DocBreak(true)) :: this
  def :/+:(hd: String): Document   = hd :: DocGroup(DocBreak(true)) :: this
  def :\:(hd: Document): Document = hd :: DocBreak(false) :: this
  def :\:(hd: String): Document   = hd :: DocBreak(false) :: this
  def :\+:(hd: Document): Document = hd :: DocGroup(DocBreak(false)) :: this
  def :\+:(hd: String): Document   = hd :: DocGroup(DocBreak(false)) :: this
  def :+:(hd: Document): Document = hd :: DocText(" ") :: this
  def :+:(hd: String): Document = hd :: DocText(" ") :: this
  def above(xs: Document) = this :: DocNewline :: xs
  def align: Document = column(k => nesting (i => nest (k - i, this)))

  type FmtState = (Int, Boolean, Document)

  /**
   * Format this document on <code>writer</code> and try to set line
   * breaks so that the result fits in <code>width</code> columns.
   *
   * @param width  ...
   * @param writer ...
   */
  def format(width: Int, writer: Writer) {

    def fits(w: Int, state: List[FmtState]): Boolean = state match {
      case _ if w < 0 => false
      case List() => true
      case (_, _, DocNil) :: z              => fits(w, z)
      case (i, b, DocCons(h, t)) :: z       => fits(w, (i,b,h) :: (i,b,t) :: z)
      case (_, _, DocText(t)) :: z          => fits(w - t.length(), z)
      case (i, b, DocNest(ii, d)) :: z      => fits(w, (i + ii, b, d) :: z)
      case (_, false, DocBreak(true)) :: z  => fits(w - 1, z)
      case (_, false, DocBreak(false)) :: z => fits(w, z)
      case (_, true, DocBreak(_)) :: z      => true
      case (_, _, DocNewline) :: z          => true
      case (i, true, DocGroup(d)) :: z      => fits(w, (i, false, d) :: z) || fits(w, (i, true, d) :: z)
      case (i, false, DocGroup(d)) :: z     => fits(w, (i, false, d) :: z)
      case (i, b, DocColumn(f)) :: z        => fits(w, (i, b, f(width - w)) :: z)
      case (i, b, DocNesting(f)) :: z       => fits(w, (i, b, f(i)) :: z)
    }

    def fmt(k: Int, state: List[FmtState]): Unit = state match {
      case List() => ()
      case (_, _, DocNil) :: z => fmt(k, z)
      case (i, b, DocCons(h, t)) :: z =>
        fmt(k, (i, b, h) :: (i, b, t) :: z)
      case (i, _, DocText(t)) :: z =>
        writer write t
        fmt(k + t.length(), z)
      case (i, b, DocNest(ii, d)) :: z =>
        fmt(k, (i + ii, b, d) :: z)
      case (i, true, DocBreak(_)) :: z =>
        writer write "\n"
        spaces(writer, i);
        fmt(i, z)
      case (i, false, DocBreak(true)) :: z =>
        writer write " "
        fmt(k + 1, z)
      case (i, false, DocBreak(false)) :: z => fmt(k, z)
      case (i, _, DocNewline) :: z =>
        writer write "\n"
        spaces(writer, i)
        fmt(i, z)
      case (i, b, DocGroup(d)) :: z =>
        val fitsFlat = fits(width - k, (i, false, d) :: z)
        fmt(k, (i, !fitsFlat, d) :: z)
      case (i, b, DocColumn(f)) :: z => fmt(k, (i, b, f(k)) :: z)
      case (i, b, DocNesting(f)) :: z => fmt(k, (i, b, f(i)) :: z)
    }

    fmt(0, (0, false, DocGroup(this)) :: Nil)
  }
  override def toString = {
    val w = new StringWriter()
    format(80, w)
    w.toString
  }
}

object Document {
  /** The empty document */
  def empty = DocNil

  def space = DocText(" ")

  /** A document which always turns into a new line */
  def hardline = DocNewline

  /** A break, which will either be turned into a line break or an empty document */
  def break = DocBreak(false)

  /** A break, which will either be turned into a line break or a space */
  def line = DocBreak(true)

  def column(f: Int => Document): Document = DocColumn(f)
  def nesting(f: Int => Document): Document = DocNesting(f)

  /** A document consisting of some text literal */
  implicit def text(s: String): Document = DocText(s)

  /**
   * A group, whose components will either be printed with all breaks
   * rendered as spaces, or with all breaks rendered as line breaks.
   */
  def group(d: Document): Document = DocGroup(d)

  /** A nested document, which will be indented as specified. */
  def nest(i: Int, d: Document): Document = DocNest(i, d)

  def ordinal(n: Int, singular: Document, plural: Document) = n match {
    case 0 => "no" :+: plural
    case 1 => "one" :+: singular
    case 2 => "two" :+: plural
    case 3 => "three" :+: plural
    case 4 => "four" :+: plural
    case 5 => "five" :+: plural
    case 6 => "six" :+: plural
    case n => text(n.toString) :+: plural
  }

  def Ordinal(n: Int, singular: Document, plural: Document) = n match {
    case 0 => "No" :+: plural
    case 1 => "One" :+: singular
    case 2 => "Two" :+: plural
    case 3 => "Three" :+: plural
    case 4 => "Four" :+: plural
    case 5 => "Five" :+: plural
    case 6 => "Six" :+: plural
    case n => text(n.toString) :+: plural
  }

  // separate a list, using an oxford or serial comma if needed
  def oxford(andOr : Document, xs: List[Document]) = xs match {
    case List() => empty
    case List(a) => a
    case List(a,b) => a :+: andOr :+: b
    case _ => fillSep(punctuate(",", xs.init)) :: "," :+: andOr :+: xs.last
  }

  def spaces(writer: Writer, n: Int) {
    var rem = n
    while (rem >= 16) { writer write "                "; rem -= 16 }
    if (rem >= 8)     { writer write "        "; rem -= 8 }
    if (rem >= 4)     { writer write "    "; rem -= 4 }
    if (rem >= 2)     { writer write "  "; rem -= 2}
    if (rem == 1)     { writer write " " }
  }

  def fold[F[_]:Foldable](f: (Document, => Document) => Document)(z: F[Document]): Document = {
    implicit val S = Semigroup instance f
    z.foldMap(some).getOrElse(empty)
  }

  def foldl[F[_]:Foldable](f: (Document, Document) => Document)(z: F[Document]): Document =
    z.foldLeft(none[Document])((od, d) => od map (f(_, d)) orElse Some(d))
     .getOrElse(empty)

  def fillSep[F[_]:Foldable](z: F[Document]): Document = fold(_ :/+: _)(z)    // fold (</>)
  def fillSepl[F[_]:Foldable](z: F[Document]): Document = foldl((a,b) => b :: group(line) :: a)(z)    // fold (</>)
  def hsep[F[_]:Foldable](z: F[Document]): Document = fold(_ :+: _)(z)       // fold (<+>)
  def vsep[F[_]:Foldable](z: F[Document]): Document = fold(_ above _)(z)     // fold (<$>)
  def vcat[F[_]:Foldable](z: F[Document]): Document = fold(_ :/: _)(z)       // fold (<$$>)
  def cat(xs: List[Document]) = group(vcat(xs))
  def fillCat[F[_]:Foldable](z: F[Document]): Document = fold(_ :/+: _)(z)   // fold (<//>)

  def softline = group(line)
  def softbreak = group(break)

  def punctuate(sep: Document, xs: List[Document]) : List[Document] = xs match {
    case List() => List()
    case List(d) => List(d)
    case d::ds => (d :: sep) :: punctuate(sep, ds)
  }
}
