package com.clarifi.reporting.ermine.parsing

import com.clarifi.reporting.ermine.Type.mkCon
import com.clarifi.reporting.ermine.Document.text
import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Diagnostic._
import scala.collection.immutable.List
import Name.{ lib, prelude }
import Type.{ subType, ftvs }
import Term._
import KindParsers._
import TypeParsers._
import TermParsers.{ literal, internalVar }
import DataConParsers.{ termOpVar }
import ParseState.Lenses._
import scalaz.{ Name => _, Arrow => _, Free => _, Forall => _, _ }
import Scalaz._

object PatternParsers {
  def unspecifiedAnnot(loc: Loc): Parser[Annot] = for {
    id <- freshId
    a = V(loc.inferred, id, None, Bound, Star(loc.inferred))
  } yield Annot(loc.inferred, List(), List(a), VarT(a))

  val patternVarName: Parser[Local] = for {
    u <- get
    p <- loc
    n <- PatternVarParsers.localName(u.canonicalTerms)
    r <- n match {
      case n : Local => unit(n)
      case _ => raise(p, "error: pattern variable shadows global binding " + n)
    }
  } yield r

  def mkLocalPatternVar(p: Loc, n: Local, a: Annot): Parser[Localized[VarP]] = for {
    id <- freshId
    l = termNames.member(n)
    v : PatternVar = V(p, id, Some(n), Bound, a)
    r = for {old <- gets(l.get(_))
             _ <- modify(l.set(_, Some(v.map(_.body)))) // should we store PatternVar?
           } yield modify(l.set(_, old))
    u <- r
  } yield Localized(VarP(v), List(n), u, r)

  val localPatternVar: Parser[Localized[VarP]] = for {
    p <- loc
    n <- patternVarName.attempt
    a <- unspecifiedAnnot(p)
    r <- mkLocalPatternVar(p, n, a)
  } yield r

  val signedLocalPatternVar: Parser[Localized[VarP]] = for {
    p <- loc
    n <- (patternVarName.attempt << keyOp(":")).attempt
    a <- annot
    r <- mkLocalPatternVar(p, n, a)
  } yield r

  val listPattern : Parser[Localized[ConP]] = for {
    nil  <- internalVar(Global("Builtin","Nil"))
    cons <- internalVar(Global("Builtin","::", InfixR(5)))
    l <- loc
    xs <- bracket(pattern sepBy comma) scope "list literal pattern"
  } yield xs.foldRight(Localized(ConP(l, nil, Nil))) {
    (cx,cy) => cx.map2(cy)((x, y) => ConP(l, cons, List(x,y)))
  }

  val productPattern: Parser[Localized[Pattern]] = for {
    p <- loc
    xs <- paren(pattern sepBy comma)
    len = xs.length
  } yield if (len == 1) xs.head
          else dist(xs) map { ProductP(p, _) }

  val lazyPattern: Parser[Localized[LazyP]]   = loc.map2(keyOp("~") >> patternL0) { (l,p) => p.map(LazyP(l,_)) }
  val strictPattern: Parser[Localized[StrictP]] = loc.map2(keyOp("!") >> patternL0) { (l,p) => p.map(StrictP(l,_)) }

  val asPattern: Parser[Localized[Pattern]] = for {
    lv <- localPatternVar
    at <- (loc ++ (keyOp("@") >> patternL0)).optional
  } yield at match {
    case None          => lv
    case Some(l ++ lp) => lv.map2(lp)(AsP(l, _, _))
  }

  val wildcardPattern: Parser[Localized[Pattern]] = for {
    p <- loc << underscore
  } yield Localized(WildcardP(p))

  // TODO: pattern parsers
  val patternL0: Parser[Localized[Pattern]] = (
    wildcardPattern |
    literal.map(lit => Localized(lit.asPattern)) | // 1, "hello", 4.0
    listPattern    | // [...]
    simpleConPattern  |
    asPattern.attempt | // v, v@Foo
    productPattern | // (a,b,c)  (a) // also deals with parenthesized patterns
    lazyPattern    | // ~
    strictPattern    // !
  ) scope "term atom"

  val simpleConPattern: Parser[Localized[ConP]] = for {
    l <- loc
    t <- DataConParsers.termVar
  } yield Localized(ConP(l, t, Nil))

  val conPattern: Parser[Localized[ConP]] = for {
    l <- loc
    t <- DataConParsers.termVar
    xs <- patternL0.many
  } yield dist(xs) map { ConP(l, t, _) }

  val patternL1: Parser[Localized[Pattern]] = conPattern | patternL0

  def patternL2 = Op.shuntingYard[Localized[Pattern]](
    for {
      l <- loc
      v <- termOpVar(Prefix(0), _ => true)
    } yield Op.unary(l, v.name.get.fixity.prec,
      (lp: Localized[Pattern]) => lp.map(p1 => ConP(v.loc, v, List(p1)))
    ),
    for {
      l <- loc
      v <- termOpVar(InfixN(0), _ => true)
    } yield v.name.get.fixity match {
      case Infix(p,a) => Op.infix(l, p, a,
        (lpx:Localized[Pattern],lpy:Localized[Pattern]) =>
          (lpx map2 lpy)((px, py) => ConP(v.loc,v, List(px,py)))
      )
      case Postfix(p) => Op.unary(l, p,
        (lp:Localized[Pattern]) => lp.map(p1 => ConP(v.loc, v, List(p1)))
      )
      case _ => sys.error("termL2: unexpected canonical fixity")
    },
    patternL1
  )


  val pattern: Parser[Localized[Pattern]] = signedLocalPatternVar | patternL2

  def manyPatterns[A](f: List[Pattern] => Parser[A]): Parser[A] = for {
    l <- loc
    ps <- patternL0.many.map(dist(_))
    r <- ps.distinct(l) >> f(ps.extract) << ps.unbind
  } yield r
}
