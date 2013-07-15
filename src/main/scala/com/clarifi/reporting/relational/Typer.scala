package com.clarifi.reporting
package relational

import PrimT._

// TODO: Fix imports - delete Scalaz._ & replace with more specific imports
import scalaz._
//import syntax.validation._
//import syntax.applicative._
import Scalaz._
import Show._
//import syntax.foldable._

object Typer {
  private def badColumns[F[+_]](cols: List[String])(implicit err: (String, String*) => F[Nothing]): F[Nothing] = {
    val errs = cols.map("Operation refers to nonexistent column (%s) in header." format _)
    err(errs.head, errs.tail:_*)
  }

  // verifies that `base` subsumes `cols` before returning `z`
  private def columnCheck[F[+_], Z](
    base: Header,
    cols: Set[ColumnName],
    z: Z
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Z] = {
    val freeRefs = cols -- base.keys
    if(freeRefs.isEmpty) z.pure[F] else badColumns(freeRefs.toList)
  }

  private def renameType[F[+_]](
    base: Header,
    attr: Attribute,
    newCol: ColumnName,
    promote: Boolean
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    def prm(ty: PrimT) = if(promote) ty.withNull else ty
    base.lift(attr.name) match {
      case Some(t) if t == attr.t => (base + (newCol -> prm(t)) - attr.name).pure[F]
      case Some(_)                => err("Inconsistent type for attribute renaming.")
      case None                   => err("Renaming non-existent attribute")
    }
  }

  private def exceptType[F[+_]](
    base: Header,
    cols: Set[ColumnName]
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    columnCheck[F, Header](base, cols, base -- cols)

  private def filterType[F[+_]](
    base: Header,
    pred: Predicate
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    columnCheck[F, Header](base, pred.columnReferences, base)

  private def combineType[F[+_]](
    base: Header,
    attr: Attribute,
    op: Op
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    columnCheck[F, Header](base, op.columnReferences, base + attr.tuple)

  private def projectType[F[+_]](
    base: Header,
    cols: Map[Attribute, Op]
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    columnCheck[F, Header](base, cols flatMap { case (attr, op) => op.columnReferences } toSet, cols.map(_._1.tuple))

  private def aggregateType[F[+_]](
    base: Header,
    attr: Attribute,
    agg: AggFunc
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    columnCheck[F, Header](base, agg.columnReferences, Map(attr.tuple))

  private def naturalJoinType[F[+_]](
    left: Header,
    right: Header
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    val joinKey = left.keySet intersect right.keySet
    val badCols = joinKey collect {
      case name if left(name) != right(name) => name -> (left(name), right(name))
    }
    if(badCols isEmpty) (left ++ right).pure[F]
    else {
      val msgs = badCols.toList.map({
        case (n, (l, r)) =>
          "Join of relations with mismatching column types: (%s, %s, %s)" format (n, l.toString, r.toString)
      })
      err(msgs.head, msgs.tail:_*)
    }
  }

  def accumulateType[F[+_]](pid: Header, nid: Header, expr: Header => F[Header], leaves: Header)
                    (implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    val v = leaves -- nid.keySet
    val v2 = expr(v)
    v2.flatMap { v2 =>
      if (v2.keySet.intersect(nid.keySet).isEmpty)
        (nid ++ v2).pure[F]
      else
        err("Subquery result of accumulate must not contain the key: %s %s".format(nid.toString, v2.toString))
    }
  }

  def groupByType[F[+_]](m: Header, key: Header, expr: Header => F[Header])(
                         implicit F: Monad[F], err: (String,String*) => F[Nothing]): F[Header] = {
    val v = m -- key.keySet
    val v2 = expr(v)
    v2.flatMap { v2 =>
      if (!v2.keySet.intersect(key.keySet).isEmpty)
        err("Subquery result of a groupBy must not contain the key: %s %s".
            format(key.toString, v2.toString))
      else (key ++ v2).pure[F]
    }
  }

  private def unionType[F[+_]](
    top: Header,
    bottom: Header,
    operation: String
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    if(top == bottom) top.pure[F]
    else {
      val msg = "Cannot %s columns: expected `" + top.toString + "', found `" + bottom.toString + "'."
      err(msg format operation)
    }
  }

  private def selectType[F[+_]](
    bases: List[Header],
    cols: Map[Attribute, Op],
    pred: Predicate
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    bases.foldLeftM(Map() : Header)(naturalJoinType[F](_,_)) flatMap
      (filterType[F](_, pred)) flatMap
      (projectType[F](_, cols))

  private def limitType[F[+_]](
    base: Header,
    start: Option[Int],
    end: Option[Int],
    order: List[(String, SortOrder)]
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    val badBounds = for {
      from <- start
      to <- end
      if from > to
    } yield "Limit's lower bound %s is after upper bound %s".format(from, to)

    badBounds match {
      case Some(s) => err(s)
      case None    => columnCheck[F, Header](base, order.map(_._1).toSet, base)
    }
  }

  def memTyperAux[F[+_], R, M](
    m: Mem[R, M],
    rtype: R => F[Header],
    mtype: M => F[Header]
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    def go(m: Mem[R, M]): F[Header] = memTyperAux(m, rtype, mtype)
    m match {
      case VarM(v)                    => mtype(v)
      case FilterM(e, pred)           => go(e) flatMap (filterType[F](_, pred))
      case CombineM(e, attr, op)      => go(e) flatMap (combineType[F](_, attr, op))
      case ExceptM(e, cs)             => go(e) flatMap (exceptType[F](_, cs))
      case ProjectM(e, cs)            => go(e) flatMap (projectType[F](_, cs))
      case AggregateM(e, attr, op)    => go(e) flatMap (aggregateType[F](_, attr, op))
      case HashInnerJoin(e1, e2)      => (go(e1) |@| go(e2))(naturalJoinType[F](_,_)).join
      case HashLeftJoin(inner, outer) => (go(inner) |@| go(outer))(naturalJoinType[F](_,_)).join // check nullability?
      case AccumulateM(pid, nid, expr, leaves, _) =>
                                         go(leaves) flatMap { hvnid => accumulateType(
                                           pid.toHeader,
                                           nid.toHeader,
                                           (hv: Header) => go(Mem.instantiate(EmptyRel(hv), expr)),
                                           hvnid
                                         )}
      case GroupByM(m, k, expr)       => go(m) flatMap (hvk => groupByType(
                                           hvk, k.map(_.tuple).toMap,
                                           (hv: Header) => go(Mem.instantiate(EmptyRel(hv), expr))))
      case MergeOuterJoin(e1, e2)     => (go(e1) |@| go(e2))(naturalJoinType[F](_,_)).join
      case EmbedMem(e)                => extTyperAux(e, rtype, mtype)
      case ProcedureCall(_, h, _, _)  => h.pure[F]
      case RenameM(m, attr, col, p)   => go(m) flatMap (renameType[F](_, attr, col, p))
      case (h:HardMem)                => h.header.pure[F]
      case LetM(r, expr) =>
        val h = extTyperAux(r, rtype, mtype)
        memTyperAux(expr, rtype, (m:MLevel[R, M]) => m match {
          case MTop => h
          case MPop(e) => go(e)
        })
    }
  }

  private def extTyperAux[F[+_], M, R](
    e: Ext[M, R],
    rtype: R => F[Header],
    mtype: M => F[Header]
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] =
    e match {
      case ExtMem(mem) => memTyperAux(mem, rtype, mtype)
      case ExtRel(rel, _) => relTyperAux(rel, rtype, mtype)
    }

  def relTyperAux[F[+_], M, R](
    rel: Relation[M, R],
    rtype: R => F[Header],
    mtype: M => F[Header]
  )(implicit F: Monad[F], err: (String, String*) => F[Nothing]): F[Header] = {
    def go(rel: Relation[M, R]): F[Header] = relTyperAux(rel, rtype, mtype)
    rel match {
      case VarR(v)                 => rtype(v)
      case Limit(r, f, t, os)      => go(r) flatMap (limitType[F](_, f, t, os))
      case Join(fst, snd)          => (go(fst) |@| go(snd))(naturalJoinType[F](_, _)).join
      case JoinOn(fst, snd, _)     => (go(fst) |@| go(snd))(_ ++ _)
      case Union(fst, snd)         => (go(fst) |@| go(snd))(unionType[F](_, _, "union")).join
      case Minus(fst, snd)         => (go(fst) |@| go(snd))(unionType[F](_, _, "subtract")).join
      case Filter(r, p)            => go(r) flatMap (filterType[F](_, p))
      case Project(r, cols)        => go(r) flatMap (projectType[F](_, cols))
      case Except(r, cols)         => go(r) flatMap (exceptType[F](_, cols))
      case Combine(r, attr, op)    => go(r) flatMap (combineType[F](_, attr, op))
      case Aggregate(r, attr, op)  => go(r) flatMap (aggregateType[F](_, attr, op))
      case SelectR(as, proj, filt) => as.traverse(go _) flatMap (selectType[F](_, proj, filt))
      case (r: HardRel)            => r.header.pure[F]
      case MemoR(r) => go(r)
      case LetR(r, expr) => for {
        h1 <- extTyperAux(r, rtype, mtype)
        h2 <- relTyperAux(expr, (r: RLevel[M, R]) => r match {
          case RTop => h1.pure[F]
          case RPop(e) => go(e)
        }, mtype)
      } yield h2
      case TableProc(args, h, _, _) =>
        TableProc.relFoldable.traverse_(args)(go(_)) >| h.toMap
    }
  }

  def augmentType(h: Header, cur: List[(String, String)], hist: List[(String, String)]): Header =
    if((cur ++ hist) isEmpty)
      h
    else {
      val ch = h + ("issueId" -> StringT(0, false)) ++
                   cur.map(p => p._1 -> StringT(0, false)) ++
                   hist.map(p => p._1 -> StringT(0, false))
      if(hist isEmpty) ch else ch + ("date" -> DateT(false))
    }

  private def nonexistentColumns(cols: List[String]) = {
    val errs = cols.map("Operation refers to nonexistent column (%s) in header." format _)
    NonEmptyList.nel(errs.head, errs.tail).failure
  }

  type TT[+A] = Either[NonEmptyList[String], A]

  private implicit def eerr(x: String, xs: String*): Either[NonEmptyList[String], Nothing] =
    Left(NonEmptyList.nel(x, xs.toList))

  def memTyper(mem: Mem[Nothing, Nothing]): TypeTag =
    Validation.fromEither(memTyperAux[TT, Nothing, Nothing](mem, x => x, x => x))

  def relTyper(rel: Relation[Nothing, Nothing]): TypeTag =
    Validation.fromEither(relTyperAux[TT, Nothing, Nothing](rel, x => x, x => x))

  def extTyper(ext: Ext[Nothing, Nothing]): TypeTag =
    Validation.fromEither(extTyperAux[TT, Nothing, Nothing](ext, x => x, x => x))

  def closedMem(mem: Mem[Nothing, Nothing]): Closed[Mem] =
    memTyper(mem).fold(e => sys.error(e.toString), x => Closed(mem, x))

  def closedRel(rel: Relation[Nothing, Nothing]): Closed[Relation] =
    relTyper(rel).fold(e => sys.error(e.toString), x => Closed(rel, x))

  def closedExt(ext: Ext[Nothing, Nothing]): Closed[Ext] =
    extTyper(ext).fold(e => sys.error(e.toString), x => Closed(ext, x))

}

