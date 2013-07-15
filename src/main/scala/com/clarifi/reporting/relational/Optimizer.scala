package com.clarifi.reporting
package relational

import ReportingUtils._
import Op._

import scalaz._
import Scalaz._
import std.map.mapKeys
//import syntax.monad._
//import syntax.monoid._
//import syntax.equal._
//import Equal._

//import std.vector._

import com.clarifi.machines._

object Optimizer {
  private type JoinKey = Set[String]

  private[this] implicit val boteq = Equal.equalA[Nothing]

  // The largest size for a literal to be considered small enough to turn into a predicate.
  private val smallLitSize = 30

  import PureSelect._

  // WOW
  def optimize(mem: Mem[Nothing, Nothing]): Mem[Nothing, Nothing] = mem

  def optimize(rel: Relation[Nothing, Nothing]): Relation[Nothing, Nothing] = {
    val (h, jh, optr) = optimizeRel[Nothing, Nothing](rel, x => x, x => x)
    impurify(optr, jh)
  }

  def optimize(ext: Ext[Nothing, Nothing]): Ext[Nothing, Nothing] =
    optimizeExt[Nothing, Nothing](ext, x => x, x => x)._2

  def optimizeExt[M: Equal, R: Equal](ext: Ext[M, R],
                                      hr: R => Header,
                                      hm: M => Header): (Header, Ext[M, R]) = ext match {
    case ExtMem(e) =>
      val h = Typer.memTyperAux[Id, R, M](e, hr, hm)(Id.id, (s1, s2) => sys.error(s1))
      (h, ExtMem(e))
    case ExtRel(r, ns) =>
      val (h, jh, r2) = optimizeRel(r, hr, hm)
      (h, ExtRel(impurify(r2, jh), ns))
  }

  /** Rewrite `outer` to operate in `inner`'s context. */
  private def flattenProjection(outer: Projection, inner: Projection): Projection =
    outer.mapValues(_.postReplace[Id](cvAttr(inner)))

  // Replaces the column references in the keys with column-valued ops.
  def cvAttr(m: Projection): Op => Op =
    mapKeys(m) { case Attribute(k, v) => Op.ColumnValue(k, v):Op } withDefault (x => x)

  /** Convert `litrel` to a predicate that works in the context of a
    * natural join.  This is not a `Relation` isomorphism, so cannot
    * be done generally; it is only safe to elide pure literal
    * relations into a containing Amalgamation with _other_ relations.
    */
  private def literalAsPredicate(litrel: NonEmptyList[Record]): Predicate =
    Predicates.any(litrel.map(Predicate.fromRecord).list)

  private def literalAsCases(jk: Set[ColumnName], litrel: NonEmptyList[Record]): Map[Attribute, Op] = {
    val preds = litrel.map(_ filterKeys jk).map(Predicate.fromRecord)
    (litrel.head.keySet -- jk).map {
      n => Attribute(n, litrel.head(n).typ) -> ((preds zip litrel).foldRight(None : Option[Op]) {
        case ((a, b), Some(r)) => Some(If(a, OpLiteral(b(n)), r))
        case ((a, b), None) => Some(OpLiteral(b(n)))
      }).get
    } toMap
  }

  def coalesceLiteral[M, R](hl: Header,
                            h: Header,
                            jh: Header,
                            ts: NonEmptyList[Record],
                            sel: SelectR[M, R]): Option[(Header, Header, SelectR[M, R])] = {
    val SelectR(rs, cs, where) = sel
    val jk = h.keySet & hl.keySet
    val functional = {
      val tks = ts map (_ filterKeys jk)
      tks.length == tks.toSet.length
    }
    val hr = h ++ hl
    if (functional) {
      val ps = literalAsPredicate(ts.map(_ filterKeys jk))
      val cases = literalAsCases(jk, ts)
      Some((hr,
            jh,
            SelectR(rs, cs ++ flattenProjection(cases, cs),
                    Predicate.And(where, ps.postReplaceOp[Id](cvAttr(cs))))))
    } else {
      None
    }
  }

  def coalesceLiterals[M, R](lits: List[(Header, NonEmptyList[Record])],
                             hhs: (Header, Header, SelectR[M, R])):
      (List[(Header, NonEmptyList[Record])], (Header, Header, SelectR[M, R])) = {
    val (work, newLits, newhhs) = lits.foldRight((false, List[(Header, NonEmptyList[Record])](), hhs)) {
      case (p@(hl, ts), (b, l, (hr, jhr, sel))) =>
        coalesceLiteral(hl, hr, jhr, ts, sel) match {
          case Some(osel) => (true, l, osel)
          case None       => (b, p :: l, (hr, jhr, sel))
        }
    }
    if(work) coalesceLiterals(newLits, newhhs) else (newLits, newhhs)
  }

  def collectJoin[M, R](rel: Relation[M, R]): List[Relation[M, R]] = rel match {
    case Join(l, r) => collectJoin(l) ++ collectJoin(r)
    case _          => List(rel)
  }

  def joinLiterals(jk: Set[String], ts1: List[Record], ts2: List[Record]): List[Record] =
    Tee.hashJoin[Record, Record, Record](_ filterKeys jk, _ filterKeys jk).
      capL(com.clarifi.machines.Source(ts1)).cap(com.clarifi.machines.Source(ts2)).foldMap {
        case (x, y) => Vector(x ++ y)
      }.toList

  def optimizeJoin[M, R](rs: List[(Header, Header, SelectR[M, R])]): (Header, Header, SelectR[M, R]) = {
    type HH[X] = (Header, Header, X)
    val (lits, cx) = rs.foldRight(List[HH[NonEmptyList[Record]]]() -> List[HH[SelectR[M, R]]]()) {
      case (p@(h, jh, r), (l, c)) => PureSelect.unapply(r, jh) match {
        case Some(SmallLit(ts)) => ((h, jh, ts) :: l, c)
        case _                  => (l, p :: c)
      }
    }
    cx match {
      case s :: ss =>
        val oss = ss.foldRight(s) {
          case ((hl, jhl, sl), (hr, jhr, sr)) => joinSelect(hl, jhl, sl, hr, jhr, sr)
        }
        val (un, css) = coalesceLiterals(lits map { case (x, _, y) => (x, y) }, oss)
        un match {
          case Nil => css
          case (x,y) :: tss =>
            val (h, jh, sel) = css
            val (hun, biglit) = tss.foldRight((x,y.list)) {
              case ((hl, tsl), (hr, tsr)) => (hl ++ hr, joinLiterals(hl.keySet & hr.keySet, tsl.list, tsr))
            }
            def hd = h ++ hun
            def mpt = (hd, hd, PureSelect(RelEmpty(hd), hd))
            biglit.toNel.map(nel => joinSelect(hun, hun, PureSelect(SmallLit(nel), hun), h, jh, sel)).getOrElse(mpt)
        }
      case Nil => lits match {
        case (h, _, ts) :: ls =>
          val (rh, rts) = ls.foldRight(h -> ts.list) {
            case ((hl, _, tsl), (hr, tsr)) => (hl ++ hr, joinLiterals(hl.keySet & hr.keySet, tsl.list, tsr))
          }
          rts.toNel.map(nel => (rh, rh, PureSelect(SmallLit(nel), rh))).getOrElse((rh, rh, PureSelect(RelEmpty(rh), rh)))
        case _ => sys.error("Panic: The impossible happened: optimizing empty joins")
      }
    }
  }

  def joinSelect[M, R](hl: Header, jhl: Header, sl: SelectR[M, R],
                       hr: Header, jhr: Header, sr: SelectR[M, R]): (Header, Header, SelectR[M, R]) = {
    val SelectR(rsl, prjl, filtl) = sl
    val SelectR(rsr, prjr, filtr) = sr
    val h = hl ++ hr
    if (joinable(jhl.keySet & jhr.keySet, prjl, prjr))
      (h, jhl ++ jhr, SelectR(rsl ++ rsr,
                              prjl ++ prjr,
                              Predicates.all(Seq(filtl, filtr))))
    else (h, h, SelectR(List(impurify(sl, jhl), impurify(sr, jhr)),
                           headerProj(h),
                           Predicate.Atom(true)))
  }

  // first turn every tableproc into a let of a tableproc
  // second lift every let out as far as it can go
  // third join all duplicate lets
  def optimizeRel[M: Equal, R: Equal](rel: Relation[M, R],
                                      hr: R => Header,
                                      hm: M => Header): (Header, Header, SelectR[M, R]) = rel match {
    case Join(l, r) => optimizeJoin((collectJoin(l) ++ collectJoin(r)).map(optimizeRel(_, hr, hm)))
    // See `joinable` for conditions under which
    // we can combine two selects into one by an
    // associative natural join.
    case JoinOn(r1, r2, cols) =>
      val (orh1, jh1, rl) = optimizeRel(r1, hr, hm)
      val (orh2, jh2, rr) = optimizeRel(r2, hr, hm)
      val h = orh1 ++ orh2
      (h, h, PureSelect(JoinOn(impurify(rl, jh1), impurify(rr, jh2), cols), h))
    // Unions can be reinterpreted as a single select if they differ only in filter.
    case Union(r1, r2) =>
      val (h, jh1, rl) = optimizeRel(r1, hr, hm)
      val (_, jh2, rr) = optimizeRel(r2, hr, hm)
      (h, h, combineFilters(rl, rr){ (l, r) =>
        Predicates.simplify(Predicate.Or(l, r))
      } getOrElse PureSelect(Union(impurify(rl, jh1), impurify(rr, jh2)), h))
    case Minus(r1, r2) =>
      val (h, jh1, rl) = optimizeRel(r1, hr, hm)
      val (_, jh2, rr) = optimizeRel(r2, hr, hm)
      (h, h, combineFilters(rl, rr){ (l, r) =>
        Predicates.simplify(Predicate.And(l, Predicate.Not(r)))
      } getOrElse PureSelect(Minus(impurify(rl, jh1), impurify(rr, jh2)), h))
    case Filter(r, p) =>
      val (h, jh, SelectR(rs, prj, filt)) = optimizeRel(r, hr, hm)
      (h, jh, SelectR(rs, prj, Predicates.simplify(Predicate.And(filt, p.postReplaceOp[Id](cvAttr(prj))))))
    case Project(r, cs) =>
      val (h, jh, SelectR(rs, prj, filt)) = optimizeRel(r, hr, hm)
      (cs.map(_._1.tuple), jh, SelectR(rs, flattenProjection(cs, prj), filt))
    case Except(r, cs) =>
      val (h, jh, SelectR(rs, prj, filt)) = optimizeRel(r, hr, hm)
      (h -- cs, jh, SelectR(rs, prj -- (cs.map(c => Attribute(c, h(c)))), filt))
    case Combine(r, attr, op) =>
      val (h, jh, SelectR(rs, prj, filt)) = optimizeRel(r, hr, hm)
      val nh = h + attr.tuple
      (nh, jh, SelectR(rs, prj + (attr -> op.postReplace[Id](cvAttr(prj))), filt))
    case Limit(r, start, end, ord) =>
      val (h, jh, or) = optimizeRel(r, hr, hm)
      (start, end) match {
        case (None, None) => (h, jh, or) // We're not actually limiting anything, so we can just pass things up.
        case _ => (h, h, PureSelect(Limit(impurify(or, jh), start, end, ord), h))
      }
    case Aggregate(r, attr, aggfunc) =>
      val (_, jh, or) = optimizeRel(r, hr, hm)
      val h = Map(attr.tuple)
      (h, h, PureSelect(Aggregate(impurify(or, jh), attr, aggfunc), h))
    case s@SelectR(rs, _, _) =>
      (headerOf(s, hr, hm), rs.map(headerOf(_, hr, hm)).foldLeft(Map():Header)(_ ++ _), s)
    case LetR(ExtMem(Literal(ts)), e) if ts.length <= smallLitSize =>
      optimizeRel[M,R](Relation.instantiate(SmallLit(ts), e), hr, hm)
    case LetR(r, e) =>
      val (h, r2) = optimizeExt(r, hr, hm)
      val (h2, _, e2) = optimizeRel[M,Option[R]](Relation.fromScope(e), (r: Option[R]) => r match {
        case None => h
        case Some(x) => hr(x)
      }, hm)
      (h2, h2, PureSelect(LetR(r2, Relation.toScope(e2)), h2))
    case MemoR(r) =>
      val (h, jh, r2) = optimizeRel(r, hr, hm)
      (h, h, PureSelect(MemoR(impurify(r2, jh)), h))
    case TableProc(args, oh, fun, ns) =>
      val h = oh.toMap
      val oargs = TableProc.relFunctor(args)(ir => optimizeRel(ir, hr, hm)._3)
      (h, h, PureSelect(TableProc(oargs, oh, fun, ns), h))
    case r =>
      implicit def iderr(x: String, xs: String*) = sys.error((x::xs.toList).mkString("\n"))
      val h = Typer.relTyperAux[Id, M, R](r, hr, hm)
      (h, h, PureSelect(r, h))
  }

  def headerOf[M, R](r: Relation[M, R], hr: R => Header, hm: M => Header): Header = {
    implicit def iderr(x: String, xs: String*) = sys.error((x::xs.toList).mkString("\n"))
    Typer.relTyperAux[Id, M, R](r, hr, hm)
  }

  private def reverseRename[K](m: Map[K, K]) =
    m map {_.swap} withDefault identity

  /**
   * Answer whether natural joins can be combined into a single `select`.
   * Rule 1: Every column in `joinKey` must appear as a ColumnValue reference in `prj1`
   * for which the `Attribute` key in prj1 also appears as a key in `prj2`.
   * Rule 2: For every key appearing in both `prj1` and `prj2`, the `Op` must be the same.
   */
  private def joinable(joinKey: JoinKey, prj1: Projection, prj2: Projection): Boolean =
    (joinKey forall { (k:ColumnName) => prj1.exists {
      case (a, ColumnValue(c, _)) => c == k && prj2.isDefinedAt(a)
      case _ => false
    }}) && ((prj1.keySet & prj2.keySet) forall { k => prj1(k) === prj2(k) })

  /** If `left` and `right` are the same except in filter, answer a
    * combination that joins the filters with `bin`, otherwise
    * None.
    */
  private def combineFilters[M: Equal, R: Equal](left: => SelectR[M, R], right: => SelectR[M, R])(
                                                 bin: (=> Predicate, => Predicate) => Predicate) =
    (left, right) match {
      case (SelectR(rs1, prj1, filt1), SelectR(rs2, prj2, filt2))
      if prj1 == prj2 && rs1 == rs2 =>
        Some(SelectR(rs1, prj1, bin(filt1, filt2)))
      case _ => None
    }
}

object PureSelect {
  def apply[M, R](r: Relation[M, R], h: Header): SelectR[M, R] =
    SelectR(List(r), headerProj(h), Predicate.Atom(true))

  def unapply[M, R](rel: Relation[M, R], h: Header) =
    rel match {
      case SelectR(List(innerRel), proj, Predicate.Atom(true))
      if headerProj(h) == proj => Some(innerRel)
      case _ => None
    }

  /** Strip all selects that don't do anything from `rel`. */
  def impurify[M, R](rel: Relation[M, R], h: Header) = {
    def recur(rel: Relation[M, R]): Relation[M, R] =
      unapply(rel, h) cata (recur, rel)
    recur(rel)
  }
}
