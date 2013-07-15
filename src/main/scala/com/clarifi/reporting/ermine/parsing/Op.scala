package com.clarifi.reporting.ermine.parsing

import com.clarifi.reporting.ermine.Diagnostic._
import com.clarifi.reporting.ermine.{ die => _, _ }
import scalaz.Ordering
import scalaz.Scalaz._
import scalaz.Ordering.{LT, GT, EQ}

sealed trait Op[T] extends Located {
  def loc: Pos
  def prec: Int
  def assoc: Assoc
  def apply(xs: List[T]): Parser[List[T]]
}

object Op {
  def unary[T](l: Pos, p: Int, f: T => T) = new Op[T] {
    def loc = l
    def prec = p
    def assoc = AssocL // permits repeated prefixes/postfixes, AssocN would disable
    def apply(xs: List[T]): Parser[List[T]] = xs match {
      case x :: xs => unit(f(x) :: xs)
      case _       => empty[Parser]
    }
  }
  def infix[T](l: Pos, p: Int, a: Assoc, f: (T,T) => T) = new Op[T] {
    def loc = l
    def prec = p
    def assoc = a
    def apply(xs: List[T]): Parser[List[T]] = xs match {
      case x :: y :: xs => unit(f(y,x) :: xs)
      case _ => empty[Parser]
    }
  }

  def shuntingYard[T](pre: Parser[Op[T]], inpost: Parser[Op[T]], operand: Parser[T]): Parser[T] = {
    def clear(l: Pos, p: Op[T], rators: List[Op[T]], rands: List[T]): Parser[T] = rators match {
      case f::fs => p.prec ?|? f.prec match {
        case LT => f(rands) flatMap { clear(l, p, fs, _) }
        case EQ => (p.assoc, f.assoc) match {
          case (AssocL, AssocL) => f(rands) flatMap { clear(l, p, fs, _) }
          case (AssocR, AssocR) => postRator(l, p :: rators, rands)
          case _ => raise(f.loc, "error: ambiguous operator of precedence " + p.prec,
                     List(p.report("note: is incompatible with this operator (add parentheses)")))
        }
        case GT => postRator(l, p :: rators, rands)
      }
      case Nil => postRator(l, List(p), rands)
    }

    def finish(l : Pos, rators: List[Op[T]], rands: List[T]): Parser[T] = rators match {
      case f :: fs => f(rands) flatMap (finish(l, fs, _))
      case Nil => rands match {
        case List(x) => unit(x)
        case _ => fail("error: ill-formed expression")
      }
    }

    def postRator(l : Pos, rators: List[Op[T]], rands: List[T]): Parser[T] =
      operand.flatMap(rand => postRand(l, rators, rand :: rands)) |
      pre.flatMap(clear(l, _, rators, rands)) |
      finish(l, rators, rands)

    def postRand(l : Pos, rators: List[Op[T]], rands: List[T]): Parser[T] =
      inpost.flatMap(clear(l, _, rators, rands)) |
      finish(l, rators, rands)

    loc.flatMap(postRator(_, List(), List()))
  }
}
