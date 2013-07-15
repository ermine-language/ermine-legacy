package com.clarifi.reporting.ermine.parsing

import com.clarifi.reporting.ermine._

import TypeNameParsers._
import ParseState.Lenses._
import scalaz.{ Free => _, _ }
import scalaz.Scalaz._

object KindParsers {
  def kindVar: Parser[V[Unit]] = for {
    p <- loc
    n <- ident
    l = kindNames.member(n)
    r <- gets(l.get(_)) flatMap {
      case Some(v) => unit(v)
      case None    => for {
        v <- freshId.map(V(p,_,Some(n),Bound,()))
        _ <- modify(l.set(_, Some(v)))
      } yield v
    }
  } yield r

  // parse a local type variable name binder
  def localKind: Parser[Localized[KindVar]] = for {
    p  <- loc
    n  <- ident
    id <- freshId
    l   = kindNames.member(n)
    v   = V(p, id, Some(n), Bound, ())
    r   = for {old <- gets(l.get(_))
                 _ <- modify(l.set(_, Some(v)))} yield modify(l.set(_, old))
    u <- r
  } yield Localized(v, List(n), u, r)

  def unspecifiedKind(loc: Loc): Parser[Kind] = for {
    id <- freshId
  } yield VarK(V(loc.inferred, id, None, Free, ())) // Free?

  def kindL0: Parser[Kind] = loc.flatMap(p =>
    as(keyOp("*"), Star(p)) |
    as(keyword("rho")|keyword("ρ"), Rho(p)) |
    as(keyword("phi")|keyword("φ"), Field(p)) |
    as(keyword("constraint")|keyword("Γ"), Constraint(p)) |
    kindVar.map(VarK(_)) |
    paren(kind)
  ) scope "kind atom"

  val arrow = (loc << keyOp("->")).map((l: Loc) => (x: Kind, y: Kind) => ArrowK(l, x, y))

  def kind: Parser[Kind] = kindL0 chainr arrow scope "kind"
}

// vim: set ts=4 sw=4 et:
