package com.clarifi.reporting.ermine.parsing

import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Diagnostic._
import com.clarifi.reporting.ermine.Document.text
import com.clarifi.reporting.ermine.Name.{ lib, prelude }
import com.clarifi.reporting.ermine.Type.{ subType, ftvs, mkCon }
import com.clarifi.reporting.ermine.Term._
import com.clarifi.reporting.ermine.syntax.Statement.{ gatherBindings, checkBindings }
import com.clarifi.reporting.ermine.parsing.TermNameParsers.{
  bindFixity, bindName, op, termName, termVar, termOpVar }
import com.clarifi.reporting.ermine.parsing.PatternParsers.{ pattern, patternL0 }
import com.clarifi.reporting.ermine.parsing.StatementParsers.{ bindingStatement }
import com.clarifi.reporting.ermine.parsing.KindParsers._
import com.clarifi.reporting.ermine.parsing.TypeParsers._
import com.clarifi.reporting.ermine.parsing.ParseState.Lenses._
import scala.collection.immutable.List
import scalaz.{ Name => _, Arrow => _, Free => _, Forall => _, _ }
import scalaz.Scalaz._


object TermParsers {

  /** This simply expects the name being looked up to exist in the parser state.
   *  The intention is that this be used for internal syntactic desugaring, so
   *  the variable should be specified by Lib already.
   */
  def internalVar(n: Name): Parser[V[Type]] = for {
    l <- loc
    n <- n match {
      case l : Local => gets(_.canonicalTerms.getOrElse(l,l))
      case g : Global => unit(g)
    }
    m <- gets(termNames.member(n).get(_))
    r <- m match {
      case Some(a) => unit(a)
      case None => warn("Missing primitive:" :+: text(n.toString)) >> empty // warn to ensure the message gets out
    }
  } yield r

  private abstract class Appable[-T, +R] {
    def apply(ts: T*): R
  }

  private def internal(n: Name): Parser[Appable[Term, Term]] =
    internalVar(n).map{nv =>
      val reloc = implicitly[Relocatable[Term]]
      val rcv = Var(nv)
      new Appable[Term, Term] {
        def apply(those: Term*) = those match {
          case Seq(fst, _*) => reloc.setLoc(rcv(those:_*), fst.loc)
          case Seq() => rcv
      }}}

  def literal: Parser[Lit[Any]] = loc.flatMap(p =>
    stringLiteral.map(LitString(p, _)) |
    token(doubleLiteral_.flatMap(d =>
      satisfy(c => c == 'F' || c == 'f').as(LitFloat(p, d.toFloat)) orElse LitDouble(p, d)
    )) |
    token(nat_.flatMap(n =>
      satisfy(c => c == 'L' || c == 'l').scope("l").as(LitLong(p, n)) |
      satisfy(c => c == 'B' || c == 'b').scope("b").as(LitByte(p, n.toByte)) |
      satisfy(c => c == 'S' || c == 's').scope("s").as(LitShort(p, n.toShort)).orElse(LitInt(p, n.toInt))
    )) |
    charLiteral.map(LitChar(p, _)) |
    dateLiteral.map(LitDate(p, _))
  ).attempt("literal")

  // TODO: factor together rec, fieldList, and relArrows

  // { foo = bar, baz = 12 }  or {}
  def rec: Parser[Term] = loc.flatMap(l => brace(
    for {
      cons <- internal(Global("Field","cons"))
      fields <- ((termVar << keyOp("=")) ++ term) sepBy comma
    } yield fields.foldRight[Term](EmptyRecord(l)) {
      case (n ++ v, r) => cons(Var(n), v, r)
    }
  )) scope "record"

  // { foo, bar, baz }  or rowEmpty
  //def fieldList: Parser[Term] = for {
  //  rowCons <- internal(Global("Relation.Row","rowCons"))
  //  rowEmpty <- internal(Global("Relation.Row","rowEmpty"))
  //  xs <- brace(term sepBy1 comma) scope "field set"
  //} yield xs.foldr(rowEmpty)(rowCons(_,_))

  def fieldList: Parser[Term] =
    brace(term sepBy comma).scope("brace literal") ++ (ch('_') >> identTail).slice.optional flatMap {
      case xs ++ module => for {
        single <- internal(Local("single_Brace" + module.map("_"+_).getOrElse("")))
        snoc <- internal(Local("snoc_Brace" + module.map("_"+_).getOrElse("")))
      } yield xs.tail.foldLeft(single(xs.head))(snoc(_,_))
    }

  // {z | x = z + 50, x > 100, y <- x}, see relation-sugar.txt
  def relArrows: Parser[Term] = envelope(for {
    arrows <- relArrow sepBy1 comma
    // always use empty list here since we are assuming all functions used in this
    // syntax use AsOp typeclass
    // TODO: should fix up desugarRelArrows to not accept this parameter
    a <- desugarRelArrows(List(), arrows)
  } yield a).scope("relation transformer")

  private val predCombs: Parser[List[V[Type]]] =
    List("<=" -> InfixN(4), ">=" -> InfixN(4),
          "<" -> InfixN(4), "==" -> InfixN(4), "!=" -> InfixN(4), ">" -> InfixN(4),
         "not" -> Idfix, "&&" -> InfixR(3), "||" -> InfixR(2)).
    traverse {case (n, fixity) =>
                internalVar(Global("Relation.Predicate", n, fixity))}

  private val opCombs: Parser[List[V[Type]]] =
    List("+" -> InfixL(6), "-" -> InfixL(6),
         "*" -> InfixL(7), "/" -> InfixL(7), "//" -> InfixL(7), "++" -> InfixL(5)).
      traverse {case (n, fixity) =>
        internalVar(Global("Relation.Op", n, fixity))
      }

  private def bindBinOps(ts: List[V[Type]]): Parser[Parser[Unit]] =
    (ts traverse (v => (bindFixity(v.name.get.local, false)
                       ++ bindName(v.name.get.local, v, termNames))
                      map {case (unfix, unmap) => unmap >> unfix})
        map (_.reverse.traverse_(identity)))

  private def bindingPredCombs[A](in: Parser[A]): Parser[A] =
    predCombs flatMap bindBinOps flatMap (in << _)

  private def bindingOpCombs[A](in: Parser[A]): Parser[A] =
    opCombs flatMap bindBinOps flatMap (in << _)

  private def relArrow: Parser[RelCata] =
    (for {to <- (termVar << keyOp("<-")).attempt
          from <- termVar} yield RenameC(to, from)) |
    (for {as <- (termVar << keyOp("=")).attempt
          op <- bindingPredCombs(bindingOpCombs(term))} yield CombineC(as, op)) |
    (bindingPredCombs(bindingOpCombs(term)) map FilterC)

  /** Insert `prim` calls for each literal with a PrimExpr variant,
    * `col` calls for each currently-bound of `initCols`, and answer
    * an expression that yields the relation catamorphism for the
    * `relArrows` form.
    *
    * We only parse to acquire bindings and erase pending free
    * variables here. */
  private def desugarRelArrows(initCols: List[Name], arrows: List[RelCata]):
  Parser[Term] = if (arrows.isEmpty) internal(Global("Function", "id")) map (_()) else {
    // shallow tree rewriting
    def rewrite(t: Term, cols: Set[Name]): Parser[Term] = {
      def rec(t: Term): Parser[Term] = t match {
        case Var(tv) if tv.name map cols getOrElse false => // TODO remove when typeclasses help us auto-colify
          internal(Global("Relation.Op", "col")) map (_(t))
        // tag literals with `prim` calls
        case t: Lit[_] =>
          internal(Global("Relation.Op", "prim")) map (_(t))
        // descent cases
        case App(f, x) => (rec(f) map2 rec(x))(App)
        case Sig(l, t, a) => rec(t) map (Sig(l, _, a))
        case Rigid(t) => rec(t) map Rigid
        // descent-stop cases
        case _: EmptyRecord | _: Product | _: Lam
           | _: Var | _: Case | _: Let | _: Hole
           | _: Remember => unit(t)
      }
      rec(t)
    }

    // rewrite a RelCata back to a term
    def catafy(arr: RelCata, cols: Set[Name]): (Parser[Term], Set[Name]) = arr match {
      case FilterC(p) =>
        (internal(Global("Relation.Predicate", "filter"))
         map2 rewrite(p, cols))(_ apply _) -> cols
      case RenameC(to, from) =>
        (internal(Global("Relation", "rename")) map (_(Var(from), Var(to))),
         cols - from.name.get + to.name.get)
      case CombineC(as, opExpr) =>
        (internal(Global("Relation.Op", "combine"))
         map2 rewrite(opExpr, cols))((comb, op) => comb(op, Var(as))) ->
        (cols + as.name.get)
    }

    arrows.tail.foldLeft(catafy(arrows.head, initCols.toSet)) {(st, arr) => st match {
      case (termAcc, cols) =>
        val (pt, nn) = catafy(arr, cols)
        (for {comp <- internal(Global("Function", ".", InfixR(9)))
              t <- pt
              prev <- termAcc}
         yield comp(t, prev)) -> nn
    }} _1
  }

  /** An endomorphism in the category of relations, minimally
    * parsed. */
  private sealed trait RelCata
  private case class FilterC(p: Term) extends RelCata
  private case class RenameC(to: TermVar, from: TermVar) extends RelCata
  private case class CombineC(as: TermVar, opExpr: Term) extends RelCata

  def listLiteral: Parser[Term] =
    bracket(term sepBy comma).scope("bracket literal") ++ (ch('_') >> identTail.slice).optional flatMap {
      case xs ++ module => for {
        nil <- internal(Local("empty_Bracket" + module.map("_"+_).getOrElse("")))
        cons <- internal(Local("cons_Bracket" + module.map("_"+_).getOrElse("")))
      } yield xs.foldRight(nil())(cons(_,_))
    }

  def caseAlt: Parser[Alt] = for {
    l <- loc
    p <- pattern << keyOp("->")
    t <- p.distinct(l) >> term << p.unbind
  } yield Alt(l,List(p.extract),t)

  def caseTerm: Parser[Term] = for {
    l <- loc << leftCase // keyword("case")
    tm <- term << right  // keyword("of")
    alts <- laidout("case alternative", caseAlt)
    // _ <- keyword("esac")
  } yield Case(l,tm,alts)

  def let: Parser[Term] = for {
    letLoc <- {loc}
    // _ <- keyword("let")
    _ <- leftLet
    bgLoc <- loc
    bs <- laidout("let binding", bindingStatement)
    (is, ss) = gatherBindings(bs)
//    bg <- mkBindingGroup(bgLoc, is, ss)
    p <- checkBindings[Parser](bgLoc, is, ss) // Annotation required here because of kind mismatch
    _ <- p.distinct(bgLoc)
    _ <- right // keyword("in")
    body <- term << p.unbind // p.unbind is just unit(()) - checkBindings isn't setting unbind, so it's using the default argument.
    // unbind let-bound vars
    l = termNames
    curBS <- gets(termNames.get(_))
    letBS = is.map(i=>i.v.name)
                  .flatten
    _ <- modify(l.set(_, curBS -- letBS))
  } yield Let(letLoc,p.extract._1,p.extract._2,body)

  /** Parser for do ... desugaring. */
  def doMonad: Parser[Term] = for {
    dbsLoc <- keyword("do") >> loc
    dbs <- laidout("do binding", doBinding) map (_.reverse)
    _ <- dbs.flatMap(_.right.toSeq).traverse_(_._2) >> // unbind all, backwards
         failWhen[Parser](dbs.isEmpty, "empty do expression") >>
         failUnless[Parser](dbs.head.isLeft, "last statement in `do' must be expression")
    mbind <- internal(Global("Syntax.Do", "bind"))
  } yield dbs.tail.foldLeft(dbs.head.left.get) {(tailAct, bform) =>
    val (mv, mf) = bform.fold(
      term => (term, Lam(tailAct.loc, WildcardP(term.loc), tailAct)),
      {case (Alt(l, ps, b), _) => (b, Lam(l, ps.head, tailAct))})
    mbind(mv, mf)
  }

  /** Parser for an effect-only action or binding. */
  def doBinding: Parser[Either[Term, (Alt, Parser[Unit])]] =
    (for {
      l <- loc
      p <- pattern
      // pretend term is to the left of the pattern
      t <- p.distinct(l) >> keyOp("<-") >> p.unbind >> term
      newUnbind <- p.rebind              // `term' invalidates p.unbind
    } yield Right(Alt(l,List(p.extract),t) -> newUnbind)) race term.map(Left.apply)

  def lam: Parser[Term] = for {
    l <- loc
    ps <- (patternL0.some << keyOp("->")).attempt.map(dist(_))
    e <- ps.distinct(l) >> term << ps.unbind
  } yield ps.extract.foldRight(e) { Lam(l, _, _) }

  def product: Parser[Term] = for {
    p <- loc
    xs <- paren(term sepBy comma)
    len = xs.length
  } yield if (len == 1) xs.head else Product(p, len)(xs:_*)

  def productSection: Parser[Term] = for {
    p <- loc
    xs <- paren(comma.many).attempt
    len = xs.length
  } yield Product(p, if (len == 0) 0 else len + 1)

  def hole: Parser[Term] = ((loc <* token("_")) map2 freshId)(
                            (loc,i) => Remember(i, Hole(loc)))

  def remember: Parser[Term] = token("?") *> ((freshId map2 bracket(term))(Remember))

  def termL0: Parser[Term] = (
    lam                 | // x -> ...
    hole                |
    remember            |
    literal             | // 1234 "hello" 'h' 12.0
    relArrows           | // [| reportId == 1234, value > 100.0 |]
    listLiteral         | // [...]
    productSection      | // (,,,)
    termVar.map(Var(_)) | // v
    product             | // ("whatever") (a,b)
    (rec race fieldList)
  ) scope "term atom"

  def termL0s = for {
    xs <- termL0.some
  } yield xs.reduceLeft(App.apply)

  // foo 5 [1,2,x]
  def termL1 = caseTerm | let | doMonad | termL0s

  def termL2 = Op.shuntingYard(
    for {
      l <- loc
      v <- termOpVar(Prefix(0), _ => true)
    } yield Op.unary(l, v.name.get.fixity.prec, (x: Term) => Var(v)(x)),
    for {
      l <- loc
      v <- termOpVar(InfixN(0), _ => true)
    } yield v.name.get.fixity match {
      case Infix(p,a) => Op.infix(l, p, a, (x:Term,y:Term) => Var(v)(x,y))
      case Postfix(p) => Op.unary(l, p, (x:Term) => Var(v)(x))
      case _ => sys.error("termL2: unexpected canonical fixity")
    },
    termL1
  )

  def termL2_ = for {
    c <- ch('-').optional.attempt
    neg <- internal(Global("Builtin", "primNeg"))
    t <- termL2
  } yield (if (c.isDefined) neg(t) else t)

  // foo 5 [1,2,x] + 12
  // def termL2 = 0.to(10).foldRight(termL1)(termExpr)

  // foo 5 [1,2,x] + 12 : Int
  def term: Parser[Term] = for {
    p <- loc
    tm <- termL2_
    // _ <- op.not // t(_ => Some(text("unknown operator")))
    r <- (keyOp(":") >> annot).map(ann => Sig(p, tm, ann)) orElse tm
  } yield r
}

