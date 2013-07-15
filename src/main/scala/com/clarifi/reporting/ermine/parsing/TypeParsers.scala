package com.clarifi.reporting.ermine.parsing

import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Diagnostic._
import com.clarifi.reporting.ermine.Document.text

import TypeNameParsers._
import KindParsers._
import ParseState.Lenses._

import scala.collection.immutable.List
import scalaz.{Name => _, Arrow => _, Free => _, Forall => _, _}
import Scalaz._

import Type.{recordT, relationT}

object TypeParsers {
  private def typeName: Parser[Name] = get.flatMap(u => name(u.canonicalTypes))
  private def localTypeName: Parser[Local] = typeName.map(_.local)

  def distinct(loc: Pos, l: List[V[Any]]) = {
    val lp = l.map(_.name)
    assert(lp.lengthCompare(lp.toSet.size) == 0) | raise(loc, text("error: duplicate variable names in binding"))
  }

  // top level definitions which bind local names
  // ->foo<- : Int
  // data ->Foo<- a b c = ->Bar<- Int a
  def typeDef: Parser[TypeVar] = for {
    p <- loc
    n <- typeName
    _ <- if (!n.isInstanceOf[Local]) raise(p, "error: type definition would shadow global type definition")
         else unit(())
    l = typeNames.member(n)
    m <- gets(l.get(_))
    r <- m match {
      case Some(v) =>
        val vp = v at p
        modify(l.set(_, Some(vp))) as vp
        // unit(v at p)
      case None => for {
        k <- unspecifiedKind(p)
        v <- freshId.map(V(p,_,Some(n),Bound,k))
        _ <- modify(l.set(_, Some(v)))
      } yield v
    }
  } yield r

  def typeVar(mk: Option[Kind] = None): Parser[V[Kind]] = for {
    p <- loc
    n <- typeName
    l = typeNames.member(n)
    m <- gets(l.get(_))
    r <- m match {
      case Some(v) => unit(v at p)
      case None => for {
        k <- mk match {
          case Some(k) => unit(k)
          case None => unspecifiedKind(p)
        }
        v <- freshId.map(V(p,_,Some(n),Bound,k))
        _ <- modify(l.set(_, Some(v)))
      } yield v
    }
  } yield r

  def typeOpVar(fix: Fixity, f: Fixity => Boolean): Parser[TypeVar] = attempt(
    for {
      p <- loc
      s <- op
      Some(n) <- gets(_.canonicalTypes.get(Local(s,fix)))
      if f(n.fixity)
      l = typeNames.member(n)
      m <- gets(l.get(_))
      r <- m match {
        case Some(v) => unit(v at p)
        case None => for {
          k <- unspecifiedKind(p)
          v <- freshId.map(V(p,_,Some(n),Bound,k))
          _ <- modify(l.set(_, Some(v)))
        } yield v
      }
    } yield r,
    fix match {
      case Idfix => "type identifier"
      case Prefix(_) => "prefix type operator"
      case _ => "type operator"
    }
  )

  def typeOp(fix: Fixity, f: Fixity => Boolean): Parser[Type] = typeOpVar(fix, f).map(VarT(_))

  val arrow: Parser[Op[Type]] = for {
    l <- loc << keyOp("->")
  } yield Op.infix(l, 0, AssocR, (a: Type, b : Type) => Arrow(l)(a,b))

  def flattenConstraints(p: Type, ys: List[Type] = List()): Option[List[Type]] = p match {
    case ProductT(_, n) if ys.length == n => Some(for {
      y <- ys
      z <- flattenConstraints(y).getOrElse(List(y))
    } yield z)
    case AppT(x,y) => flattenConstraints(x, y :: ys)
    case _ => None
  }
  def doubleArrow: Parser[Op[Type]] = for {
    l <- loc << keyOp("=>")
  } yield Op.infix(l, 0, AssocR, (x: Type, y: Type) => flattenConstraints(x) match {
    case Some(xs) => Forall(l, List(), List(), Exists.mk(l, List(), xs), y)
    case None => Forall(l, List(), List(), x, y)
  })

  def partition: Parser[Op[Type]] = for {
    l <- loc << keyOp("<-")
  } yield Op.infix(l, 1, AssocN, (x: Type,y: Type) => flattenConstraints(y) match {
    case Some (ys) => Part(l.inferred, x, ys)
    case None => Part(l.inferred, x, List(y))
  })

  // signatures as well
  def localType(defaultKind: (Pos => Parser[Kind]) = unspecifiedKind): Parser[Localized[V[Kind]]] = for {
    p <- loc
    n ++ k <- (localTypeName ++ defaultKind(p)) |
         paren(localTypeName ++ (colon >> kind))
    id <- freshId
    l = typeNames.member(n)
    v = V(p, id, Some(n), Bound, k)
    r = for {old <- gets(l.get(_))
             _ <- modify(l.set(_, Some(v)))} yield modify(l.set(_, old))
    u <- r
  } yield Localized(v, List(n), u, r)

  def localTypes[A](f: List[V[Kind]] => Parser[A], defaultKind: (Pos => Parser[Kind]) = unspecifiedKind): Parser[A] = for {
    l <- loc
    ts <- localType(defaultKind).many.map(dist(_))
    r <- ts.distinct(l) >> f(ts.extract) << ts.unbind
  } yield r

  def unspecifiedType(loc: Loc): Parser[Type] = for {
    id <- freshId
  } yield VarT(V(loc.inferred, id, None, Free, Star(loc.inferred)))

  def rho(l: Loc): Parser[Type] = {
    def f(mod: String): Name => Name = {
      case l : Local => l.global(mod)
      case n         => n
    }

    ( for {
        lp <- ellipsis >> loc
        v <- typeVar(Some(Rho(lp.inferred)))
      } yield VarT(v)
    ) |
    gets(_.moduleName).flatMap( mod =>
      typeName.sepBy(comma).map(xs => ConcreteRho(l,xs.map(f(mod)).toSet))
    )
  } scope "row type"


  def typL0: Parser[Type] = loc.flatMap(l =>
    banana(rho(l)) |
    brace(rho(l)).map((recordT at l)(_)) |
    bracket(rho(l)).map((relationT at l)(_)) |
    paren(
      keyOp("->").as(Arrow(l)) |
      comma.many.map(xs => if (xs.length == 0) ProductT(l, 0) else ProductT(l, xs.length + 1))
    ).attempt |
    typeVar().map(VarT(_)) |
    paren(anyTyp.sepBy1(comma)).map(xs => if (xs.length == 1) xs.head else ProductT(l, xs.length)(xs :_ *))
  ) scope "type atom"
  def typL1: Parser[Type] = typL0.some.map(_.reduceLeft(AppT.apply))

  def typL2 = Op.shuntingYard(
    for {
      l <- loc
      v <- typeOpVar(Prefix(0), _ => true)
    } yield Op.unary(l, v.name.get.fixity.prec, (x: Type) => VarT(v)(x)),
    arrow | doubleArrow | partition |
    (for {
      l <- loc
      v <- typeOpVar(InfixN(0), _ => true)
    } yield v.name.get.fixity match {
      case Infix(p,a) => Op.infix(l, p, a, (x:Type,y:Type) => VarT(v)(x,y))
      case Postfix(p) => Op.unary(l, p, (x:Type) => VarT(v)(x))
      case _ => sys.error("typL2: unexpected canonical fixity")
    }),
    typL1
  )

  def manyDistinct[A](p: Parser[Localized[A]]): Parser[Localized[List[A]]] = for {
    l <- loc
    las <- p.many.map(dist(_))
    _ <- las.distinct(l)
  } yield las

  def kQuant(q: Parser[Any]): Parser[Localized[(List[KindVar], List[TypeVar])]] = for {
    _ <- q
    olks <- brace(manyDistinct(localKind)).optional
    ots  <- manyDistinct(localType()).optional
    _ <- keyOp(".")
    _ <- if (!olks.isDefined && !ots.isDefined)
             Diagnostic.fail("empty quantifier")
         else unit(())
  } yield olks.getOrElse(Localized(List())) ++ ots.getOrElse(Localized(List()))

  def uQuant: Parser[Localized[(List[KindVar], List[TypeVar])]] = kQuant(keyword("forall"))

  def nf(t: Type): Parser[Type] = Parser((st, su) => Pure(t.nf(su)))

  def typ: Parser[Type] = (loc ++ uQuant.optional ++ typL2 flatMap {
    case l ++ q ++ t => q match {
      case Some(ls) => ls.unbind >> nf(Forall(l, ls.extract._1, ls.extract._2, Exists(l), t))
      case None     => nf(t)
    }
  } scope "type")

  def exists = for {
    l <- loc
    xs <- keyword("exists") >> localType().many << keyOp(".")
    lxs = dist(xs)
    body <- lxs.distinct(l) >> typL2.sepBy1(comma) << lxs.unbind
  } yield Exists(l, lxs.extract, body)

  def anyTyp = exists | typ

  def annot: Parser[Annot] = for {
    l <- loc
    lus <- kQuant(keyword("some")).optional.map(_.getOrElse(Localized((List(), List()))))
    body <- typ << lus.unbind
  } yield Annot(l, lus.extract._1, lus.extract._2, body)
}
