package com.clarifi.reporting
package relational

import com.clarifi.reporting._
import com.clarifi.reporting.sql._
import com.clarifi.reporting.backends._
import com.clarifi.reporting.Reporting._
import com.clarifi.reporting.util.PartitionedSet
import DB._
import PrimT._
import ReportingUtils.simplifyPredicate
import SqlPredicate._
import SqlExpr.compileOp

import scalaz._
import scalaz.IterV._
import scalaz.Id._
//import Scalaz.{^ => _, _}
import scalaz.std.indexedSeq.{toNel => _, _}
import scalaz.std.vector.{toNel => _, _}
import scalaz.std.map._
import scalaz.std.function._
import scalaz.std.option._
import scalaz.std.list._
import scalaz.std.string._
import scalaz.std.anyVal._

import scalaz.syntax.monad._
import scalaz.syntax.traverse.{ToFunctorOps => _, _}

import com.clarifi.machines._
import Plan.awaits
import Tee.{ right, left }

import org.apache.log4j.Logger
import com.clarifi.reporting.util.PimpedLogger._

case class SqlPrg(h: Header,
                  prg: List[SqlStatement],
                  q: SqlQuery,
                  refl: Reflexivity[ColumnName])

case class MemPrg(h: Header,
                  prg: List[SqlStatement],
                  p:  OrderedProcedure[DB, Record],
                  refl: Reflexivity[ColumnName])

class SqlScanner(implicit emitter: SqlEmitter) extends Scanner[DB] {

  private[this] def logger = Logger getLogger this.getClass

  import AggFunc._

  private[this] def fillTable(table: TableName, header: Header, from: SqlQuery
                             ): List[SqlStatement] = {
    val c = SqlCreate(table = table, header = header)
    List(c, SqlInsert(table, c.hints.sortColumns(header.keySet), from))
  }

  // `attr`: The codomain attribute
  def compileAggFunc(attr: Attribute, f: AggFunc, attrs: String => SqlExpr): SqlExpr = f match {
    case Count => FunSqlExpr("COUNT", List(Verbatim("*")))
    case Sum(x) => FunSqlExpr("SUM", List(compileOp(x, attrs)))
    case Avg(x) => FunSqlExpr("AVG", List(compileOp(x, attrs)))
    case Min(x) => FunSqlExpr("MIN", List(compileOp(x, attrs)))
    case Max(x) => FunSqlExpr("MAX", List(compileOp(x, attrs)))
    /** @todo MSP - SQLite does not support STDDEV or VAR, work around somehow? */
    case Stddev(x) => emitter.emitStddevPop(compileOp(x, attrs))
    case Variance(x) => emitter.emitVarPop(compileOp(x, attrs))
  }

  val exec = new SqlExecution()
  import exec._


  def sequenceSql(p : List[SqlStatement]) : DB[Unit] = p.distinct.traverse_ {
    case SqlLoad(tn, h, pc) => bulkLoad(h, tn, pc)
    case SqlIfNotExists(tn,stats) => {
      val tecol = "tableExists"
      val sql = emitter.checkExists(tn, tecol)
      logger ltrace ("Executing sql: " + sql.run)
      catchException(DB.transaction(withResultSet(sql, rs => {
        rs.next() && (rs.getObject(tecol) ne null)
      }.point[DB]).flatMap(b => if (!b) sequenceSql(stats) else ().point[DB])))
      .map(_ fold (e => logger error ("While executing: " + e.getMessage),
                   identity))
    }
    //TODO write job to clean out old memos
    case x =>
      val sql = x.emitSql(emitter)
      logger ltrace ("Executing sql: " + sql.run)
      DB.executeUpdate(sql)
  }

  def scanMem[A:Monoid](m: Mem[Nothing, Nothing],
                        f: Process[Record, A],
                        order: List[(String, SortOrder)] = List()): DB[A] = {
    implicit val sup = Supply.create
    compileMem(Optimizer.optimize(m), (x:Nothing) => x, (x: Nothing) => x) match {
      case MemPrg(h, p, q, rx) => for {
        _ <- sequenceSql(p)
        a <- q(order) map (_ andThen f execute)
      } yield a
    }
  }

  def scanRel[A:Monoid](m: Relation[Nothing, Nothing],
                        f: Process[Record, A],
                        order: List[(String, SortOrder)] = List()): DB[A] = {
    implicit val sup = Supply.create
    compileRel(Optimizer.optimize(m), (x:Nothing) => x, (x: Nothing) => x) match {
      case SqlPrg(h, p, q, rx) => for {
	_ <- sequenceSql(p)
        a <- scanQuery(orderQuery(q, order), h) map (_ andThen f execute)
      } yield a
    }
  }

  def scanExt[A:Monoid](m: Ext[Nothing, Nothing],
                        f: Process[Record, A],
                        order: List[(String, SortOrder)] = List()): DB[A] = m match {
      case ExtRel(r, db) => scanRel(r, f, order)
      case ExtMem(mem) => scanMem(mem, f, order)
    }

  def guidName = "t" + sguid
  def freshName(implicit sup: Supply) = "t" + sup.fresh

  def orderQuery(sql: SqlQuery, order: List[(String, SortOrder)])(implicit sup: Supply): SqlQuery = sql match {
    case sel : SqlSelect if sel.attrs.size > 0 && sel.limit == (None, None) =>
      sel copy (
        orderBy = order collect {
          case (col, ord) if (sel.attrs.get(col) map (_.deparenthesize) match {
             case None | Some(LitSqlExpr(_)) => false
             case Some(_) => true
           }) => sel.attrs(col) -> ord(SqlAsc, SqlDesc)
        }
      )
    case _ if order.nonEmpty =>
      val s = freshName
      SqlSelect(
        tables = Map(TableName(s) -> sql),
        orderBy = order.map { case (col, ord) => ColumnSqlExpr(TableName(s), col) -> ord(SqlAsc, SqlDesc) }
      )
    case _ => sql
  }

  import SortOrder._

  def compileMem[M,R](m: Mem[R, M], smv: M => MemPrg, srv: R => SqlPrg)(implicit sup: Supply): MemPrg =
    m match {
      case VarM(v) => smv(v)
      case LetM(ext, expr) =>
        val p = ext match {
          case ExtMem(e) => compileMem(e, smv, srv)
          case ExtRel(e, _) => {
            val SqlPrg(h, ps, q, rx) = compileRel(e, smv, srv)
            MemPrg(h, ps, o => scanQuery(orderQuery(q, o), h), rx)
          }
        }
        val MemPrg(h, ps, pop, rx) = p
        val ep = compileMem(expr, (v: MLevel[R, M]) => v match {
            case MTop => MemPrg(h, List(), pop, rx)
            case MPop(mex) => compileMem(mex, smv, srv)
          }, srv)
        ep copy (prg = ps ++ ep.prg)
      case EmbedMem(ExtMem(e)) => compileMem(e, smv, srv)
      case EmbedMem(ExtRel(e, _)) => // TODO: Ditto
        val SqlPrg(h, ps, q, rx) = compileRel(e, smv, srv)
        MemPrg(h, ps, o => scanQuery(orderQuery(q, o), h), rx)
      case CombineM(e, attr, op) =>
        val MemPrg(h, ps, q, rx) = compileMem(e, smv, srv)
        MemPrg(h + (attr.name -> attr.t), ps, o =>
          if (!o.toMap.contains(attr.name))
            q(o).map(_.map(t => t + (attr.name -> op.eval(t))))
          else {
            val oo = o takeWhile { case (n, _) => n != attr.name }
            q(oo).map(_ map (t => t + (attr.name -> op.eval(t))) andThen sorting(oo, o))
          }, rx combineAll(Map(attr.name -> op), { case x => x }, x => x))
      case AggregateM(e, attr, op) =>
        val MemPrg(h, ps, q, rx) = compileMem(e, smv, srv)
        MemPrg(Map(attr.name -> attr.t),
               ps,
               _ => q(List()) map (_ andThen reduceProcess(op, attr.t).outmap(p => Map(attr.name -> p))),
               ForallTups(Map(attr.name -> None), PartitionedSet.zero))
      case FilterM(m, p) =>
        val MemPrg(h, ps, q, rx) = compileMem(m, smv, srv)
          MemPrg(h, ps,
                 o => q(o) map (_ andThen Process.filtered(Predicates.toFn(simplifyPredicate(p, rx)))),
                 rx && Predicates.constancies(p))
      case MergeOuterJoin(m1, m2) =>
        val r1 = compileMem(m1, smv, srv)
        val r2 = compileMem(m2, smv, srv)
        val MemPrg(h1, p1, q1, rx1) = r1
        val MemPrg(h2, p2, q2, rx2) = r2
        val jk = h1.keySet intersect h2.keySet
        MemPrg(h1 ++ h2, p1 ++ p2, o => {
          val prefix = o takeWhile (x => jk contains x._1)
          val preo = prefix ++ jk.view.filterNot(prefix.toMap.contains).map(_ -> Asc)
          val ord: Order[Record] = recordOrd(preo)
          val merged = ^(q1(preo), q2(preo))(
            (q1p, q2p) => q1p.tee(q2p)(Tee.mergeOuterJoin((r: Record) => r filterKeys jk,
                                                          (r: Record) => r filterKeys jk
                                                          )(ord)).map {
            case This(a) => (h2 map (kv => kv._1 -> NullExpr(kv._2))) ++ a
            case That(b) => (h1 map (kv => kv._1 -> NullExpr(kv._2))) ++ b
            case Both(a, b) => a ++ b
          })
          if (prefix == o) merged else merged map (_ andThen sorting(prefix, o))
        }, rx1 && rx2)
      case HashInnerJoin(m1, m2) =>
        val r1 = compileMem(m1, smv, srv)
        val r2 = compileMem(m2, smv, srv)
        val MemPrg(h1, p1, q1, rx1) = r1
        val MemPrg(h2, p2, q2, rx2) = r2
        val jk = h1.keySet intersect h2.keySet
        MemPrg(h1 ++ h2,
               p1 ++ p2,
               o => {
                 val os = o.toMap.keySet
                 val o1 = os -- h1.keySet
                 val o2 = os -- h2.keySet
                 val prefix1 = o takeWhile (x => h1.keySet(x._1))
                 val prefix2 = o takeWhile (x => h2.keySet(x._1))
                 if (o1.isEmpty)
                   hashJoin(q2(List()), q1(o), jk)
                 else if (o2.isEmpty)
                   hashJoin(q1(List()), q2(o), jk)
                 else if (prefix1.length > prefix2.length)
                   hashJoin(q2(List()), q1(prefix1), jk) map (_ andThen sorting(prefix1, o))
                 else
                   hashJoin(q1(List()), q2(prefix2), jk) map (_ andThen sorting(prefix2, o) )},
               rx1 && rx2)
      case HashLeftJoin(inner, outer) =>
        val MemPrg(hin,  pin,  qin,  rxin)  = compileMem(inner, smv, srv)
        val MemPrg(hout, pout, qout, rxout) = compileMem(outer, smv, srv)
        val jk = hin.keySet intersect hout.keySet
        val nulls : Record = hout collect {
          case (col, ty) if !(jk contains col) => col -> NullExpr(ty)
        }
        MemPrg(hin ++ hout,
               pin ++ pout,
               o => {
                 val pfx = o takeWhile(x => hin.keySet(x._1))
                 if (pfx.length == o.length) // no sorting needed
                   leftHashJoin(qin(o), qout(List()), jk, nulls)
                 else
                   leftHashJoin(qin(pfx), qout(List()), jk, nulls) map (_ andThen sorting(pfx, o))
               },
               rxin && rxout)
      case AccumulateM(parentIdCol, nodeIdCol, expr, l, t) =>
        val MemPrg(ht,pt,qt,rt) = compileMem(t, smv, srv)
        val MemPrg(hl,pl,ql,rl) = compileMem(l, smv, srv)
        val accumProc: OrderedProcedure[DB,Record] = {
          (ord: List[(String, SortOrder)]) => (db: java.sql.Connection) =>
            // read both the tree and leaves into memory because working on this in a streaming
            // fashion is difficult
            var leaves = Map[PrimExpr, Record]() // map from nid to (|..nid..v|)
            var tree   = Map[PrimExpr, Record]() // map from nid to (|..nid..pid..k|)
            qt(List())(db).foreach( rec => tree = tree + (rec(nodeIdCol.name) -> rec) )
            ql(List())(db).foreach( rec => leaves = leaves + (rec(nodeIdCol.name) -> rec) )

            // map from nid to all of the leaves in its subtree
            // for example, the root node will have every list
            var descendantLeaves: Map[PrimExpr, Vector[Record]] = Map().withDefaultValue(Vector())
            // for each leaf, recursively add itself to its parent, grandparent, (great^n)grandparent's list
            def insertIntoDescendantLeaves(parentId: PrimExpr, leaf: Record): Unit = {
              // Make sure the leaf's parent exists in the tree, because a leaf could be an orphan
              // and it doesn't make sense to add orphans to descendantLeaves
              tree.get(parentId) foreach { parent =>
                descendantLeaves = descendantLeaves + (parentId -> (descendantLeaves(parentId) :+ leaf))
                val grandParentId = parent(parentIdCol.name)
                if( tree.contains(grandParentId) ) // Are we at the root node yet?
                  insertIntoDescendantLeaves(grandParentId, leaf)
              }
            }
            leaves.foreach { case (nid,leaf) =>
              insertIntoDescendantLeaves( leaf(nodeIdCol.name), leaf )
            }
            descendantLeaves.view.map { case (nid, leafVec) =>
              val leafRec = Literal( NonEmptyList( leafVec.head, leafVec.tail: _* ) )
              val subquery = Mem.instantiate(leafRec, expr)
              val MemPrg(sh, sp, sq, sr) = compileMem(subquery, smv, srv)
              if (!sp.isEmpty)
                sys.error("subqueries of groupBy cannot 'let' new temp tables: " + subquery)
              else {
                val nodeTup = (nodeIdCol.name -> nid)
                sq(List())(db).map(_ + nodeTup)
              }
            }.foldLeft(Mem.zeroProcedure[Record])((p1,p2) => Mem.append(p1,p2)).
              andThen(sorting(List(), ord))
        }
        implicit def err(s: String, msgs: String*): Option[Nothing] = None
        val hdr = Typer.accumulateType[Option](
          parentIdCol.toHeader, nodeIdCol.toHeader,
          v => Typer.memTyper(Mem.instantiate(EmptyRel(v), expr).substPrg(srv, smv)).toOption,
          Typer.memTyper(l.substPrg(srv,smv)).toOption.get).get
        MemPrg(hdr, pt ++ pl, accumProc, rt.filterKeys((k:String) => k == nodeIdCol.name))
      case GroupByM(m, k, expr) =>
        def toOp(a: Attribute) = Op.ColumnValue(a.name, a.t)
        val MemPrg(h, p, q, r) = compileMem(m, smv, srv)
        val knames = k.map(_.name).toSet
        val joined: OrderedProcedure[DB, Record] = {
          (ord: List[(String, SortOrder)]) => (db: java.sql.Connection) =>
             val kord_ = ord.filter { p => knames.contains(p._1) }
             val kord = kord_ ++ (knames -- kord_.map(_._1)).map(n => (n, SortOrder.Asc))
             val v2ord = ord filterNot (kord_ contains)
             // this will actually run the outermost query, but this is prob
             // fine, since we are guarded by a function
             val rows: Procedure[scalaz.Id.Id, Record] = Mem.join { q(kord)(db).
               andThen(
                 Process.groupingBy((r: Record) => r.filterKeys(knames.contains))).
               map { case (key, recs) =>
                 val x = Literal(NonEmptyList(recs.head, recs.tail: _*))
                 val subquery = Mem.instantiate(x, expr)
                 val MemPrg(sh, sp, sq, sr) = compileMem(subquery, smv, srv)
                 if (!sp.isEmpty)
                   sys.error("subqueries of groupBy cannot 'let' new temp tables: " + subquery)
                 else
                   sq(v2ord)(db).map(_ ++ key)
               }
             }
             rows andThen sorting(kord ++ v2ord, ord)
        }
        implicit def err(s: String, msgs: String*): Option[Nothing] = None
        val hdr = Typer.groupByType[Option](
          h, k.map(_.tuple).toMap,
          v => Typer.memTyper(Mem.instantiate(EmptyRel(v), expr).substPrg(srv, smv)).toOption).get
        MemPrg(hdr, p, joined, r.filterKeys(knames.contains))
      case ProcedureCall(args, h, proc, namespace)  => sys.error("TODO")
      case l@Literal(ts) => MemPrg(l.header, List(),
        so => com.clarifi.machines.Source.source(sort(ts.list, so)).idProcedure.point[DB],
        Reflexivity literal ts)
      case EmptyRel(h) => MemPrg(h, List(), _ => Machine.stopped.idProcedure.point[DB], KnownEmpty())
      case QuoteMem(n) => sys.error("Cannot scan quotes.")
      case ExceptM(m, cs) =>
        val MemPrg(h, p, q, rx) = compileMem(m, smv, srv)
        MemPrg(h -- cs, p, q andThen (_ andThen (_ map ((t: Record) => t -- cs))), rx)
      case ProjectM(m, cs) =>
        val MemPrg(h, p, q, rx) = compileMem(m, smv, srv)
        MemPrg(cs.map(_._1.tuple), p, q andThen (_ andThen (_ map ((t: Record) => cs.map {
          case (attr, op) => attr.name -> op.eval(t)
        }))), combineAll(rx, cs))
      case x => sys.error("inconceivable! " + x)
  }

  private def hashJoin(q1: DB[Procedure[Id, Record]], q2: DB[Procedure[Id, Record]], jk: Set[String]) =
    ^(q1, q2)((q1, q2) => q1.tee(q2)(Tee.hashJoin(_ filterKeys jk, _ filterKeys jk)).map(p => p._1 ++ p._2))

  private def leftHashJoin(dq1: DB[Procedure[Id, Record]],
                           dq2: DB[Procedure[Id, Record]],
                           jk: Set[String],
                           nulls: Record): DB[Procedure[Id, Record]] = {
    def build(m: Map[Record, Vector[Record]]): Plan[T[Record, Record], Nothing, Map[Record, Vector[Record]]] =
      (for {
        rr <- awaits(right[Record])
        k = rr filterKeys jk
        mp <- build(m.updated(k, m.getOrElse(k, Vector.empty) :+ rr))
      } yield mp) orElse Return(m)
    def augments(m: Map[Record, Vector[Record]], r: Record): Vector[Record] = m.lift(r filterKeys jk) match {
      case None => Vector(r ++ nulls)
      case Some(v) => v map (r ++ _)
    }
    def emits(v: Vector[Record]): Plan[T[Record, Record], Record, Unit] =
      v.foldr[Plan[T[Record, Record], Record, Unit]](Return(()))(e => k => Emit(e, () => k))
    ^(dq1, dq2)((q1, q2) =>
      q1.tee(q2)(build(Map()) flatMap { m =>
        awaits(left[Record]) flatMap { r =>
          emits(augments(m, r))
        } repeatedly
      }))
  }

  private def filterRx(rx: Reflexivity[ColumnName], p: Predicate) =
      rx && Predicates.constancies(p)

  private def distinctness(h: Header, rx: Reflexivity[ColumnName], cols: Map[Attribute, Op]): Set[String] =
    rx match {
      case KnownEmpty() => Set()
      case ForallTups(_, _) =>
        if ((h.keySet diff rx.consts.keySet) forall (c =>
             cols exists {
               case (_, op) => preservesDistinctness(rx, op, c)
             })) Set() else Set("distinct")
    }

  /** @todo SMRC Since this was written, the op language has changed
    *       such that this answers true too often.
    */
  private def preservesDistinctness(rx: Reflexivity[ColumnName], op: Op, col: ColumnName): Boolean = {
    val ms = op.foldMap((c: ColumnName) => Map(c -> 1))
    ms.get(col).map(_ == 1).getOrElse(false) && ms.keySet.forall(c => c == col || rx.consts.isDefinedAt(c))
  }

  private def combineAll(rx: Reflexivity[ColumnName],
                         comb: Map[Attribute, Op],
                         keepOld: Boolean = false) =
    rx combineAll (mapKeys(comb)(_.name), {case x => x}, identity, keepOld)

  def compileRel[M,R](m: Relation[M, R], smv: M => MemPrg,
                                    srv: R => SqlPrg)(implicit sup: Supply): SqlPrg = {

    def mkUnion(l: Relation[M, R], r: Relation[M, R], op: (SqlQuery, SqlQuery) => SqlQuery) = {
      val lc = compileRel(l, smv, srv)
      val rc = compileRel(r, smv, srv)
      val SqlPrg(h1, p1, q1, refl1) = lc
      val SqlPrg(h2, p2, q2, refl2) = rc
      SqlPrg(h1, p1 ++ p2, op(q1, q2), refl1 || refl2)
    }

    def columns(h: Header, rv: TableName) = h.map(x => (x._1, ColumnSqlExpr(rv, x._1)))
    m match {
      case VarR(v) => srv(v)
      case Join(l, r) =>
        val SqlPrg(h1, p1, q1, refl1) = compileRel(l, smv, srv)
        val SqlPrg(h2, p2, q2, refl2) = compileRel(r, smv, srv)
        val jn = (q1, q2) match {
          case (SqlJoin(xs, ul), SqlJoin(ys, _)) => SqlJoin(xs append ys, ul)
          case (SqlJoin(xs, ul), _) =>
            SqlJoin(xs append NonEmptyList((q2, TableName(freshName), h2)), ul)
          case (_, SqlJoin(ys, ur)) =>
            SqlJoin((q1, TableName(freshName), h1) <:: ys, ur)
          case (_, _) =>
            val un = freshName
            val ul = freshName
            val ur = freshName
            SqlJoin(NonEmptyList((q1, TableName(ul), h1), (q2, TableName(ur), h2)), TableName(un))
        }
        SqlPrg(h1 ++ h2, p1 ++ p2, jn, refl1 && refl2)
      case JoinOn(l, r, on) =>
        val lc = compileRel(l, smv, srv)
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val ul = freshName
        val ur = freshName
        val SqlPrg(h1, p1, q1, refl1) = lc
        val SqlPrg(h2, p2, q2, refl2) = rc
        SqlPrg(h1 ++ h2,
               p1 ++ p2,
               SqlJoinOn((q1, TableName(ul), h1), (q2, TableName(ur), h2), on, TableName(un)),
               refl1 && refl2)
      case Union(l, r) => mkUnion(l, r, SqlUnion(_, _))
      case Minus(l, r) =>
        val lc = compileRel(l, smv, srv)
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val ul = freshName
        val ur = freshName
        val SqlPrg(h, p1, q1, refl1) = lc
        val SqlPrg(_, p2, q2, refl2) = rc
        SqlPrg(h, p1 ++ p2,
               SqlExcept(q1, TableName(ul), q2, TableName(ur), h), refl1 || refl2)
      case Filter(r, pred) =>
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val SqlPrg(h, p, q, rx) = rc
        val pred1 = simplifyPredicate(pred, rx)
        SqlPrg(h, p, q match {
          case v:SqlSelect if (v.limit._1.isEmpty && v.limit._2.isEmpty) =>
            v.copy(criteria = compilePredicate(pred1, v.attrs) :: v.criteria)
          case _ => SqlSelect(tables = Map(TableName(un) -> q),
                              attrs = columns(h, TableName(un)),
                              criteria = List(compilePredicate(pred1, ColumnSqlExpr(TableName(un), _))))
        }, filterRx(rx, pred))
      case Project(r, cols) =>
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val SqlPrg(h, p, q, rx) = rc
        SqlPrg(cols.map(_._1.tuple),
               p,
               SqlSelect(tables = Map(TableName(un) -> q),
                         attrs = { val as = columns(h, TableName(un))
                                   cols map { case (attr, op) =>
                                     (attr.name -> compileOp(op, as)) }}),
               combineAll(rx, cols))
      case Aggregate(r, attr, f) =>
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val SqlPrg(h, p, q, _) = rc
        SqlPrg(Map(attr.name -> attr.t), p, q match {
          case v:SqlSelect if v.limit == (None, None) =>
            v.copy(attrs = Map(attr.name -> compileAggFunc(attr, f, v.attrs)))
          case _ => SqlSelect(tables = Map(TableName(un) -> q),
                              attrs = Map(attr.name -> compileAggFunc(attr, f, columns(h, TableName(un)))))
        }, ForallTups(Map(attr.name -> None), PartitionedSet.zero))
      case Except(r, cs) =>
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val SqlPrg(h, p, q, rx) = rc
        SqlPrg(h -- cs, p, SqlSelect(tables = Map(TableName(un) -> q),
                                     attrs = columns(h, TableName(un)) -- cs),
                                     rx filterKeys (!cs.contains(_)))
      case Combine(r, attr, op) =>
        val rc = compileRel(r, smv, srv)
        val un = freshName
        val SqlPrg(h, p, q, rx) = rc
        SqlPrg(h + attr.tuple, p, SqlSelect(tables = Map(TableName(un) -> q),
                                            attrs = {
                                              val as = columns(h, TableName(un))
                                              as + (attr.name -> compileOp(op, as)) }),
                                  combineAll(rx, Map(attr -> op), true))
      case Limit(r, from, to, order) =>
        val rc = compileRel(r, smv, srv)
        val u1 = freshName
        val u2 = freshName
        val SqlPrg(h, p, q, rx) = rc
        SqlPrg(h, p, emitter.emitLimit(q, h, TableName(u1), from, to, (toNel(order.map {
          case (k, v) => ColumnSqlExpr(TableName(u1), k) -> v.apply(
            asc = SqlAsc,
            desc = SqlDesc
          )}).map(_.list).getOrElse(
            h.keys.map(k => (ColumnSqlExpr(TableName(u1), k), SqlAsc)).toList)), TableName(u2)), rx)
      case Table(h, n) => SqlPrg(h, List(), FromTable(n, h.keys.toList), Reflexivity.zero)
      case TableProc(args, oh, src, namespace) =>
        val h = oh.toMap
        val argable = TableProc.argFunctor.map(args){case (typeName, r) =>
          (TableName(guidName, List(), TableName.Variable(typeName)),
           compileRel(r, smv, srv))}
        val un = guidName
        val sink = TableName(un, List(), TableName.Temporary)
        SqlPrg(h, TableProc.argFoldable.foldMap(argable)(_._2.prg.toIndexedSeq)
                  :+ SqlCreate(table = sink, header = h)
                  :+ SqlExec(sink, src, namespace,
                             TableProc.argFoldable.foldMap(argable){
                               case (unt, SqlPrg(ih, _, iq, _)) =>
                                 fillTable(unt, ih, iq)
                             }, oh map (_._1),
                             argable map (_ bimap (_._1,
                                                   SqlExpr.compileLiteral)))
                 toList,
               FromTable(sink, h.keys.toList),
               Reflexivity.zero)
      case RelEmpty(h) =>
        val un = guidName
        SqlPrg(h, List(SqlCreate(table = TableName(un, List(), TableName.Temporary),
                                 header = h)),
               FromTable(TableName(un, List(), TableName.Temporary), h.keys.toList), KnownEmpty())
      case QuoteR(_) => sys.error("Cannot scan quotes")
      case l@SmallLit(ts) =>
        import com.clarifi.machines.Source
        val h = l.header
        val un = guidName
        SqlPrg(h,
               List(SqlCreate(table = TableName(un, List(), TableName.Temporary),
                              header = h),
                    SqlLoad(TableName(un, List(), TableName.Temporary), h, Source.source(ts.toList).idProcedure.point[DB])),
               FromTable(TableName(un, List(), TableName.Temporary), h.keys.toList),
               Reflexivity literal ts)
      case MemoR(r) => {
	val rc = compileRel(r,smv,srv)
	val relHash = "MemoHash_" + r.##.toString
	val myTN = TableName(relHash, List(), TableName.Persistent)
	val fillStat = fillTable(myTN, rc.h, rc.q)
	val myPrg = List(SqlIfNotExists(myTN,rc.prg ++ fillStat))
	SqlPrg(rc.h, myPrg, FromTable(myTN, rc.h.keys.toList), rc.refl)
      }
      case LetR(ext, exp) =>
        val un = guidName
        val tup = ext match {
          case ExtRel(rel, _) => // TODO: Handle namespace
            val rc = compileRel(rel, smv, srv)
            val SqlPrg(ih, ip, iq, rx) = rc
            (ih, rx, ip ++ fillTable(TableName(un, List(), TableName.Temporary),
                                     ih, iq))
          case ExtMem(mem) =>
            val m =compileMem(mem, smv, srv)
            val MemPrg(h, p, pop, rx) = m
            (h, rx, p ++ List(SqlCreate(table = TableName(un, List(), TableName.Temporary), header = h),
                              SqlLoad(TableName(un, List(), TableName.Temporary), h, pop(List()))))
        }
        val (ih, rx1, ps) = tup
        val ec = compileRel(exp, smv, (v: RLevel[M,R]) => v match {
          case RTop => SqlPrg(ih, List(), FromTable(TableName(un, List(), TableName.Temporary), ih.keys.toList), rx1)
          case RPop(e) => compileRel(e, smv, srv)
        })
        val SqlPrg(h, p, q, rx2) = ec
        SqlPrg(h, ps ++ p, q, rx2)
      case SelectR(rs, cs, where) =>
        // Here be dragons.
        val prgs = rs.map(compileRel(_, smv, srv))
        val (stmts, hs, qs, rx) = prgs.foldRight((List[SqlStatement](),
                                                  List[Header](),
                                                  List[SqlQuery](),
                                                  Reflexivity.zero[ColumnName])) {
          case (SqlPrg(h, stmts, q, rx), (astmts, hs, qs, rxs)) =>
            (stmts ++ astmts, h :: hs, q :: qs, rx && rxs)
          }
        val hsp = hs.map(h => freshName -> h)
        val rx1 = filterRx(rx, where)
        val rx2 = combineAll(rx1, cs)
        val columnLocs: Map[ColumnName, List[String]] =
          hsp.toIterable flatMap {
            case (subUn, h) => h.keys map (_ -> subUn)
          } groupBy (_._1) mapValues (_ map (_._2) toList)
        val lookupColumn = (c:ColumnName) => ColumnSqlExpr(TableName(columnLocs(c).head), c)
        val h = hs.foldRight(Map():Header)(_ ++ _)
        SqlPrg(cs.map(_._1.tuple),
               stmts,
               SqlSelect(options = distinctness(h, rx1, cs),
                         attrs = cs.map {
                           case (attr, op) => attr.name -> compileOp(op, lookupColumn)
                         },
                         tables = (hsp zip qs) map {
                           case ((un, _), q) => TableName(un) -> q
                         } toMap,
                         criteria = compilePredicate(simplifyPredicate(where, rx),
                                                     lookupColumn) :: (for {
                                      natJoin <- columnLocs
                                      (colName, sources) = natJoin
                                      natJoinAtom <- sources zip sources.tail
                                      (l, r) = natJoinAtom
                                    } yield SqlEq(ColumnSqlExpr(TableName(l), colName),
                                                  ColumnSqlExpr(TableName(r), colName))).toList), rx2)
    }
  }
}
