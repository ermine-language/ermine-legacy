package com.clarifi.reporting
package relational

import scalaz._
import Scalaz._
import IterV._

import com.clarifi.reporting.SortOrder._

import com.clarifi.machines._
import com.clarifi.machines.Source._

object ScannerState {
  type S = Map[TableName, StateEntry]
  type BS[A] = S => A
}

case class StateEntry(header: Header, records: List[Record]) {
  def ++(s: StateEntry): StateEntry = StateEntry(header, records ++ s.records)
  def --(s: StateEntry): StateEntry = StateEntry(header, records filterNot (s.records contains _))
}

import ScannerState._

class StateScanner extends Scanner[BS] {

  def scanMem[A:Monoid](m: Mem[Nothing, Nothing],
                        f: Process[Record, A],
                        order: List[(String, SortOrder)] = List()) =
    scanMemAux(m, (x: Nothing) => x, (x: Nothing) => x).map {
      case StateEntry(h, ts) => (f cap source(sort(ts, order))).foldMap(x => x)
    }

  def scanRel[A:Monoid](m: Relation[Nothing, Nothing],
                        f: Process[Record, A],
                        order: List[(String, SortOrder)] = List()) =
    scanExt(ExtRel(m, ""), f, order)

  def scanExt[A:Monoid](m: Ext[Nothing, Nothing],
                        f: Process[Record, A],
                        order: List[(String, SortOrder)] = List()) =
    scanMem(EmbedMem(m), f, order)

  def scanMemAux[R,M](m: Mem[R, M],
                      smv: M => BS[StateEntry],
                      srv: R => BS[StateEntry]): BS[StateEntry] = m match {
    case VarM(v) => smv(v)
    case LetM(ext, exp) => for {
      memo <- ext match {
        case ExtRel(rel, _) => scanRel(rel, smv, srv) // TODO: Do something with database name
        case ExtMem(mem) => scanMemAux(mem, smv, srv)
      }
      r <- scanMemAux(exp, (x: MLevel[R, M]) => x match {
          case MTop => memo.pure[BS]
          case MPop(v) => scanMemAux(v, smv, srv)
        }, srv)
    } yield r
    case FilterM(m, p) => scanMemAux(m, smv, srv) map {
      case StateEntry(h, t) => StateEntry(h, t filter Predicates.toFn(p))
    }
    case ExceptM(m, cs) => scanMemAux(m, smv, srv) map {
      case StateEntry(h, ts) =>
      StateEntry(h -- cs, ts.map(_ filterKeys (x => !cs(x))))
    }
    case ProjectM(m, cs) => scanMemAux(m, smv, srv) map {
      case StateEntry(h, ts) =>
      StateEntry(h filterKeys (x => cs.keySet.map(_.name).contains(x)), ts.map(_ filterKeys cs.keySet.map(_.name)))
    }
    case CombineM(m, c, op) => scanMemAux(m, smv, srv) map {
      case StateEntry(h, ts) =>
      StateEntry(h + (c.name -> c.t), ts.map(t => t + (c.name -> op.eval(t))))
    }
    case AggregateM(m, attr, agg) => scanMemAux(m, smv, srv) map {
      case StateEntry(h, ts) =>
        StateEntry(Map(attr.name -> attr.t), List(Map(attr.name -> AggFunc.reduce[List](agg, attr.t).apply(ts))))
    }
    case RenameM(m, attr, col, p) => scanMemAux(m, smv, srv) map {
      case StateEntry(h, ts) =>
        def promote(t: PrimT) = if(p) t.withNull else t
        StateEntry(h.map { case (k, t) => if(k == attr.name) (col, promote(t)) else (k, t) },
                   ts.map(t => t mapKeys (k => if(k == attr.name) col else k)))
    }
    case HashInnerJoin(fst, snd) => for {
      sfst <- scanMemAux(fst, smv, srv)
      ssnd <- scanMemAux(snd, smv, srv)
      jk = sfst.header.keySet intersect ssnd.header.keySet
    } yield joinOnH(sfst, ssnd, jk map (x => (x, x)))
    case MergeOuterJoin(fst, snd) => for {
      sfst <- scanMemAux(fst, smv, srv)
      ssnd <- scanMemAux(snd, smv, srv)
      jk = sfst.header.keySet intersect ssnd.header.keySet
    } yield StateEntry(sfst.header ++ ssnd.header,
              Tee.mergeOuterJoin[Record, Record, Record](_ filterKeys jk, _ filterKeys jk).
                capL(source(sort(sfst.records, jk.toList.map(x => x -> Asc)))).
                cap( source(sort(ssnd.records, jk.toList.map(x => x -> Asc)))).foldMap {
                  case This(a) => List(ssnd.header.map(p => p._1 -> NullExpr(p._2)) ++ a)
                  case That(b) => List(sfst.header.map(p => p._1 -> NullExpr(p._2)) ++ b)
                  case Both(a, b) => List(a ++ b)
                })
    case EmbedMem(ExtMem(m)) => scanMemAux(m, smv, srv)
    case EmbedMem(ExtRel(r, _)) => scanRel(r, smv, srv) // TODO: Handle the database name somehow
    case ProcedureCall(_,_,_,_) => sys.error("Procedures not supported by State")
    case Literal(ts) => StateEntry(ts.head.map { case (k, v) => (k, v.typ) }, ts.list).pure[BS]
    case EmptyRel(h) => StateEntry(h, List()).pure[BS]
    case QuoteMem(_) => sys.error("Quotes not supported by State")
  }

  def joinOnH(s1: StateEntry, s2: StateEntry, on: Set[(String, String)]): StateEntry = {
    val onp = on.toList.unzip
    def f(cs: List[String])(x: Record, y: Record) = cs.foldRight(true) { (c, b) =>
      if (x(c) < y(c)) true else
      if (x(c) > y(c)) false else b
    }
    val m1 = s1.records.groupBy(a => onp._1.map(a(_)))
    StateEntry(s1.header ++ s2.header, s2.records.flatMap(x => m1(onp._2.map(x(_))) map (x ++ _)))
  }

  def scanRel[M,R](m: Relation[M, R], smv: M => BS[StateEntry], srv: R => BS[StateEntry]): BS[StateEntry] = m match {
    case VarR(v) => srv(v)
    case Join(fst, snd) => for {
      sfst <- scanRel(fst, smv, srv)
      ssnd <- scanRel(snd, smv, srv)
      jk = sfst.header.keySet intersect ssnd.header.keySet
    } yield joinOnH(sfst, ssnd, jk map (x => (x, x)))
    case JoinOn(fst, snd, cols) => for {
      sfst <- scanRel(fst, smv, srv)
      ssnd <- scanRel(snd, smv, srv)
    } yield joinOnH(sfst, ssnd, cols)
    case Union(fst, snd) => for {
      sfst <- scanRel(fst, smv, srv)
      ssnd <- scanRel(snd, smv, srv)
    } yield sfst ++ ssnd
    case Minus(fst, snd) => for {
      sfst <- scanRel(fst, smv, srv)
      ssnd <- scanRel(snd, smv, srv)
    } yield sfst -- ssnd
    case Filter(rel, pred) => scanRel(rel, smv, srv).map(x =>
      x.copy(records = x.records.filter(Predicates.toFn(pred))))
    case Project(rel, cols) => scanRel(rel, smv, srv) map (ts =>
      StateEntry(cols.map(_._1.tuple), ts.records.map(t => cols.map {
        case (attr, op) => attr.name -> op.eval(t)}))
    )
    case Limit(rel, from, to, order) => scanRel(rel, smv, srv) map {
      case StateEntry(h, ts) => {
        val sorted = sort(ts, order)
        val realFrom = from.map(x => (x - 1) max 0) getOrElse 0
        StateEntry(h, to match {
          case None => sorted.drop(realFrom)
          case Some(y) => sorted.drop(realFrom).take(y - realFrom)
        })
      }
    }
    case Aggregate(rel, attr, agg) => scanRel(rel, smv, srv) map {
      case StateEntry(h, ts) => StateEntry(Map(attr.name -> attr.t),
          List(Map(attr.name -> AggFunc.reduce[List](agg, attr.t).apply(ts))))
    }
    case LetR(ext, exp) => for {
      memo <- ext match {
        case ExtRel(rel, _) => scanRel(rel, smv, srv) // TODO: Handle database name somehow
        case ExtMem(mem) => scanMemAux(mem, smv, srv)
      }
      r <- scanRel(exp, smv, (x: RLevel[M, R]) => x match {
          case RTop => memo.pure[BS]
          case RPop(v) => scanRel(v, smv, srv)
        })
    } yield r
    case Table(h, n) => _(n)
    case TableProc(args, h, src, namespace) => sys.error("Not having any table fun.")
    case RelEmpty(h) => StateEntry(h, List()).pure[BS]
    case QuoteR(n) => sys.error("Cannot scan quotes.")
    case l@SmallLit(ts) => StateEntry(l.header, ts.toList).pure[BS]
    case _ => sys.error("State backend does not support operation.")
  }
}

