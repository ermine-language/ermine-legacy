package com.clarifi.reporting
package sql

import java.util.{Date,UUID}
import scalaz._
import scalaz.Scalaz._

import com.clarifi.reporting.{ Header, TableName }

import RawSql._

sealed abstract class SqlOrder {
  def emitSql: RawSql = this match {
    case SqlAsc => "asc"
    case SqlDesc => "desc"
  }
}
case object SqlAsc extends SqlOrder
case object SqlDesc extends SqlOrder

sealed abstract class SqlPredicate {
  /** Emit a predicate for a where clause */
  def emitSql(implicit emitter: SqlEmitter): RawSql = this match {
    case SqlTruth(t) => if (t) "'A' = 'A'" else "'A' = 'B'"
    case SqlLt(a, b) => raw("(") |+| a.emitSql(emitter) |+| ") < (" |+| b.emitSql(emitter) |+| ")"
    case SqlGt(a, b) => raw("(") |+| a.emitSql(emitter) |+| ") > (" |+| b.emitSql(emitter) |+| ")"
    case SqlEq(a, b) => raw("(") |+| a.emitSql(emitter) |+| ") = (" |+| b.emitSql(emitter) |+| ")"
    case SqlLte(a, b) => raw("(") |+| a.emitSql(emitter) |+| ") <= (" |+| b.emitSql(emitter) |+| ")"
    case SqlGte(a, b) => raw("(") |+| a.emitSql(emitter) |+| ") >= (" |+| b.emitSql(emitter) |+| ")"
    case SqlNot(a) => raw("not (") |+| a.emitSql(emitter) |+| ")"
    case SqlOr(h, t @ _*) => raw("(") |+| t.foldLeft(h.emitSql(emitter))((a, b) =>
      a |+| " or " |+| b.emitSql(emitter)) |+| raw(")")
    case SqlAnd(h, t @ _*) => raw("(") |+| t.foldLeft(h.emitSql(emitter))((a, b) =>
      a |+| " and " |+| b.emitSql(emitter)) |+| raw(")")
    case SqlIsNull(e) => raw("(") |+| e.emitSql(emitter) |+| ") is null"
    case ExistsSqlExpr(query) => raw("exists ") |+| query.emitSql(emitter)
  }
}
case class SqlTruth(truth: Boolean) extends SqlPredicate
case class SqlLt(left: SqlExpr, right: SqlExpr) extends SqlPredicate
case class SqlGt(left: SqlExpr, right: SqlExpr) extends SqlPredicate
case class SqlEq(left: SqlExpr, right: SqlExpr) extends SqlPredicate
case class SqlLte(left: SqlExpr, right: SqlExpr) extends SqlPredicate
case class SqlGte(left: SqlExpr, right: SqlExpr) extends SqlPredicate
case class SqlNot(p: SqlPredicate) extends SqlPredicate
case class SqlOr(ps: SqlPredicate*) extends SqlPredicate
case class SqlAnd(ps: SqlPredicate*) extends SqlPredicate
case class SqlIsNull(expr: SqlExpr) extends SqlPredicate
case class ExistsSqlExpr(query: SqlQuery) extends SqlPredicate

object SqlPredicate {
  /** Compile a `predicate`, delegating column reference expression
    * compilation to `lookupColumn`.
    */
  def compilePredicate(predicate: Predicate,
                       lookupColumn: String => SqlExpr)(
                       implicit emitter: SqlEmitter): SqlPredicate = {
    def subop(op: Op) = SqlExpr.compileOp(op, lookupColumn)
    predicate.apply[SqlPredicate](
      atom = b => SqlTruth(b),
      lt = (s1, s2) => SqlLt(subop(s1), subop(s2)),
      gt = (s1, s2) => SqlGt(subop(s1), subop(s2)),
      eq = (s1, s2) => SqlEq(subop(s1), subop(s2)),
      not = e => SqlNot(e),
      or = SqlOr(_, _),
      and = SqlAnd(_, _),
      isNull = e => SqlIsNull(subop(e)))
  }
}

sealed abstract class SqlExpr {
  import scalaz.std.iterable._

  import SqlExpr._

  def emitSql(implicit emitter: SqlEmitter): RawSql = this match {
    case ColumnSqlExpr(table,column) => emitter.emitQualifiedColumnName(table, column)
    case BinSqlExpr(op, e1, e2) => raw("(") |+| e1.emitSql(emitter) |+| ") " |+| op |+| " (" |+| e2.emitSql(emitter) |+| ")"
    case PrefixSqlExpr(op, e1) => raw(op) |+| " (" |+| e1.emitSql(emitter) |+| ")"
    case PostfixSqlExpr(e1, op) => e1.emitSql(emitter) |+| " " |+| op
    case FunSqlExpr(fn, args) => raw(fn) |+| "(" |+| args.map(_.emitSql(emitter)).toIterable.rawMkString(", ") |+| ")"
    case IntervalExpr(n, u) => emitter.emitInterval(n, u)
    case LitSqlExpr(lit) => lit.emitSql(emitter)
    case CaseSqlExpr(clauses, otherwise) =>
      (raw("(case ") |+| clauses.map{case (t, c) =>
        raw("when ") |+| t.emitSql(emitter) |+| raw(" then ") |+| c.emitSql(emitter)}
       .rawMkString(" ")
       |+| raw(" else ") |+| otherwise.emitSql(emitter) |+| raw(" end)"))
    case ParensSqlExpr(e1) => raw("(") |+| e1.emitSql(emitter) |+| ")"
    case OverSqlExpr(e1, over) => emitter.emitOver(e1, over)
    case Verbatim(s) => s
  }

  @annotation.tailrec
  final def deparenthesize: SqlExpr = this match {
    case ParensSqlExpr(e) => e.deparenthesize
    case e => e
  }
}
case class ColumnSqlExpr(table: TableName, column: SqlColumn) extends SqlExpr
case class BinSqlExpr(f: String, a: SqlExpr, b: SqlExpr) extends SqlExpr
case class PrefixSqlExpr(f: String, arg: SqlExpr) extends SqlExpr
case class PostfixSqlExpr(arg: SqlExpr, f: String) extends SqlExpr
case class FunSqlExpr(f: String, args: List[SqlExpr]) extends SqlExpr
case class IntervalExpr(n: Int, units: TimeUnit) extends SqlExpr
case class LitSqlExpr(get: SqlLiteral) extends SqlExpr
case class CaseSqlExpr(clauses: NonEmptyList[(SqlPredicate, SqlExpr)],
                       otherwise: SqlExpr) extends SqlExpr
case class ParensSqlExpr(get: SqlExpr) extends SqlExpr
case class OverSqlExpr(e: SqlExpr, over: List[(SqlExpr, SqlOrder)]) extends SqlExpr
case class Verbatim(sql: String) extends SqlExpr

object SqlExpr {
  def columns(h: Header, rv: TableName) = h.map(x => (x._1, ColumnSqlExpr(rv, x._1)))
  def columns(h: List[String], rv: TableName) = h.map(x => (x, ColumnSqlExpr(rv, x))).toMap

  /** Compile an `op`, delegating column reference expression
    * compilation to `lookupColumn`.
    */
  def compileOp(op: Op, lookupColumn: String => SqlExpr)(implicit emitter: SqlEmitter): SqlExpr = {
    import Op._
    def rec(op: Op): SqlExpr = op match {
      case OpLiteral(lit) => compileLiteral(lit)
      case ColumnValue(cn, _) => lookupColumn(cn)
      case Add(a, b) =>
        BinSqlExpr("+", rec(a), rec(b))
      case Sub(a, b) =>
        BinSqlExpr("-", rec(a), rec(b))
      case Mul(a, b) =>
        BinSqlExpr("*", rec(a), rec(b))
      case FloorDiv(a, b) =>
        BinSqlExpr(emitter.emitIntegerDivisionOp, rec(a), rec(b))
      case DoubleDiv(a, b) =>
        BinSqlExpr("/", rec(a), rec(b))
      case Pow(a, b) =>
        /**
         * @todo MSP - SQLite does not support POWER, work around somehow?
         *
         * SMB: No. I doubt we'll be using sqlite beyond test cases,
         * and there are already things with it that bust. I am of the
         * opinion we should just not sweat it.
         */
        FunSqlExpr("POWER", List(rec(a), rec(b)))
      case Concat(as) =>
        emitter.emitConcat(as.map(rec))
      case If(test, conseq, altern) => (rec(conseq), rec(altern)) match {
        case (cConseq, CaseSqlExpr(clauses, oth)) =>
          CaseSqlExpr((SqlPredicate.compilePredicate(test, lookupColumn),
                       cConseq) <:: clauses, oth)
        case (CaseSqlExpr(clauses, oth), cAltern) =>
          CaseSqlExpr((SqlPredicate.compilePredicate(Predicate.Not(test), lookupColumn),
                       cAltern) <:: clauses, oth)
        case (cConseq, cAltern) =>
          CaseSqlExpr(NonEmptyList((SqlPredicate.compilePredicate(test, lookupColumn),
                                    cConseq)),
                      ParensSqlExpr(cAltern))
      }
      case Coalesce(l, r) =>
        FunSqlExpr("coalesce", List(rec(l),rec(r)))
      case DateAdd(d, n, u) =>
        FunSqlExpr(emitter.emitDateAddName, List(rec(d), IntervalExpr(n, u)))
      case Funcall(name, db, ns, args, _) =>
        FunSqlExpr(emitter emitProcedureName (name, ns) run,
                   args map rec)
    }
    rec(op)
  }

  def compileLiteral(e: PrimExpr): SqlExpr = e match {
    case StringExpr(_,s) => LitSqlExpr(SqlString(s))
    case ByteExpr(_,b) => LitSqlExpr(SqlByte(b))
    case ShortExpr(_,s) => LitSqlExpr(SqlShort(s))
    case IntExpr(_,i) => LitSqlExpr(SqlLong(i))
    case LongExpr(_,l) => LitSqlExpr(SqlLong(l))
    case DoubleExpr(_,d) => LitSqlExpr(SqlDouble(d))
    case DateExpr(_,d) => LitSqlExpr(SqlDate(d))
    case BooleanExpr(_,b) => LitSqlExpr(SqlBool(b))
    case UuidExpr(_,u) => LitSqlExpr(SqlUuid(u))
    case NullExpr(_) => LitSqlExpr(SqlNull)
  }
}

sealed abstract class SqlLiteral {
  def emitSql(implicit emitter: SqlEmitter): RawSql = this match {
    case SqlString(s) => raw("'") |+| s.replace("'","''") |+| "'"
    case SqlBool(b) => emitter.emitBoolean(b)
    case SqlInt(i) => i.toString
    case SqlLong(l) => l.toString
    case SqlDouble(d) => d.toString
    case SqlByte(b) => b.toString
    case SqlShort(s) => s.toString
    case SqlDate(d) => emitter.emitDate(d)
    case SqlUuid(u) => emitter.emitUuid(u)
    case SqlNull => emitter.emitNull
  }
}
case class SqlString(get: String) extends SqlLiteral
case class SqlBool(get: Boolean) extends SqlLiteral
case class SqlByte(get: Byte) extends SqlLiteral
case class SqlShort(get: Short) extends SqlLiteral
case class SqlInt(get: Int) extends SqlLiteral
case class SqlLong(get: Long) extends SqlLiteral
case class SqlDouble(get: Double) extends SqlLiteral
case class SqlDate(get: Date) extends SqlLiteral
case class SqlUuid(get: UUID) extends SqlLiteral
case object SqlNull extends SqlLiteral

