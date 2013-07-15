package com.clarifi.reporting.ermine.parsing

import scalaz.{Name => _, _}
import Scalaz.{modify => _, _}

import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Diagnostic._
import com.clarifi.reporting.ermine.Document.text
import ParseState.Lenses._

/** Parsers for dealing with DMTL identifiers and keywords
  *
  * @author EAK
  */

abstract class NameParser {
  def identStart : Parser[Char]
  def opStart: Parser[Char]

  def ident : Parser[Local] = token(
    (for {
      l <- loc
      i <- (setBol(false) >> identStart >> identTail).slice
      if (!keywords(i))
    } yield Local(i)
    ).attempt("identifier")
  )

  /** parse an operator (without trailing whitespace!) */
  def op: Parser[String] = token((for {
      i <- (opStart >> opChar.skipMany >> (ch('_') >> tailChar.skipSome).skipOptional).slice
      _ <- if(i == "|") notFollowedBy("]")
           else if(keyOps(i)) fail("key operator")
           else if(i.length > 2 && i.foldLeft(true)((b, a) => b && a == '-')) fail("comment")
           else unit(())
  } yield i).attempt("operator"))

  def opName[N](m: PartialFunction[Local,N]) = for {
    x <- (
      (keyword("prefix") >> op).map(prefix(_)) |
      (keyword("postfix") >> op).map(postfix(_)) |
      op.map(infix(_))
    ).attempt
    r <- liftOption(m.lift(x)) | fail("forward reference to an operator with unknown precedence")
  } yield r

  def name[N>:Local](m: PartialFunction[Local,N]): Parser[N] = (
    ident.map(n => m.lift(n).getOrElse(n)) | paren(opName(m)).attempt) scope "name"

//  def localName(l: Lens[ParseState, Map[Local,Name]]): Parser[Localized[Local]] = for {
//    m <- gets(l.get)
//    val lookup = (n: Local) => m.getOrElse(n,n).local
//    n <- ident |
//         paren(
//           (keyword("prefix") >> prec.optional ++ op).map({
//             case Some(n) ++ r => prefix(r,n)
//             case None ++ r => lookup(prefix(r))
//           }) |
//           (keyword("postfix") >> prec.optional ++ op).map({
//             case Some(n) ++ r => postfix(r,n)
//             case None ++ r => lookup(postfix(r))
//           }) |
//           (keyword("infixl") >> prec map2 op)((n,r) => infix(r,n,AssocL)) |
//           (keyword("infixr") >> prec map2 op)((n,r) => infix(r,n,AssocR)) |
//           (keyword("infix")  >> prec map2 op)((n,r) => infix(r,n,AssocN)) |
//           op.map(r => lookup(infix(r)))
//         )
//    val lp = l.member(n)
//    _ <- modify(lp.set(_, Some(n)))
//  } yield Localized(n, List(n), modify(lp.set(_, m.lift(n))))

  // also returns the previous name for restoration purposes if found
  def localName[N>:Local](m: PartialFunction[Local,N]): Parser[N] = {
    def lookup(n: Local) = m.lift(n).getOrElse(n)
    ident.map(lookup(_)) |
    paren(
      (keyword("prefix") >> prec.optional ++ op).map({
        case Some(n) ++ r => prefix(r,n)
        case None ++ r => lookup(prefix(r))
      }) |
      (keyword("postfix") >> prec.optional ++ op).map({
        case Some(n) ++ r => postfix(r,n)
        case None ++ r => lookup(postfix(r))
      }) |
      (keyword("infixl") >> prec map2 op)((n,r) => infix(r,n,AssocL)) |
      (keyword("infixr") >> prec map2 op)((n,r) => infix(r,n,AssocR)) |
      (keyword("infix")  >> prec map2 op)((n,r) => infix(r,n,AssocN)) |
      op.map(r => lookup(infix(r)))
    )
  }

  /** Bind `n` to `v` in outer parser, reverse in inner. */
  def bindName[A](n: Local, v: V[A], l: Lens[ParseState, Map[Name, V[A]]]): Parser[Parser[Unit]] = {
    val lp = l member n
    ((parsing.gets(lp.get) << modify(x => lp.set(x, Some(v)))) map (old => modify(x => lp.set(x, old))))
  }

  def addFixity(n: Local, ty: Boolean): Parser[Unit] = {
    def add(l: Lens[ParseState, Map[Local,Name]]) = {
      gets(l.member(n).get) flatMap {
        case Some(_) => fail("Multiple fixity definitions for operator: " + n.toString)
        case None    => bindFixity(n, ty).skip
      }
    }
    if (ty) add(canonicalTypes) else add(canonicalTerms)
  }

  /** Answer a Parser that binds `n` to type or term fixities, whose
    * inner Parser undoes the binding. */
  def bindFixity(n: Local, ty: Boolean): Parser[Parser[Unit]] = {
    def add(l: Lens[ParseState, Map[Local,Name]]) = {
      val lp = l.member(n)
      for {old <- gets(lp.get) << modify(s => lp.set(s, Some(n)))}
      yield modify(lp.set(_, old))
    }
    if (ty) add(canonicalTypes) else add(canonicalTerms)
  }

  // a few term related concerns, becuase we need them across datacons and pattern vars
}

object TypeNameParsers extends NameParser {
  def identStart = letter
  def opStart = opChar
}
