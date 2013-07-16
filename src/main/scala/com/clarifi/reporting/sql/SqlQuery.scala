package com.clarifi.reporting.sql

import scalaz._
import Scalaz._
import Equal._
import Show._

import com.clarifi.reporting.{ Header, TableHints, Hints, TableName, ColumnName }

// A Data Type for SQL Queries
sealed abstract class SqlQuery {

  import RawSql._
  import scalaz.std.iterable._

  /**
   * Compiles a SqlQuery to a SQL statement that can then be run
   * The method assumes that all special cases (Sqlone)
   * have already been handled and thus can be safely ignored.
   *
   * @todo rob: groupBy
   */
  def emitSql(implicit emitter: SqlEmitter): RawSql = this match {
    case SqlSelect(options, attrs, tables, criteria, groupBy, orderBy, limit) =>
      raw("select ") |+|
      (if (options contains "distinct") raw("distinct ") else raw("")) |+|
      { if (attrs.size == 0) "*"
        else (attrs.toIndexedSeq.sortBy((_: (SqlColumn, SqlExpr))._1)
              .map(x => raw("(") |+| x._2.emitSql |+| ") " |+|
                   emitter.emitColumnName(x._1)).rawMkString(", ")) } |+|
      (if (tables.size > 0) {
        raw(" from ") |+| tables.map(x => x._2.emitSubquery |+|
                                     " " |+| emitter.emitTableName(x._1)).rawMkString(", ")
                                 } else emitter.emitFromEmptyTable ) |+|
      (if (criteria.size > 0)
        raw(" where ") |+| criteria.map(x => raw("(") |+| x.emitSql |+| ")").toIterable.rawMkString(" and ")
      else raw("")) |+|
      (if (orderBy.size > 0)
        raw(" order by ") |+| orderBy.map(x => x._1.emitSql |+| " " |+| x._2.emitSql).toIterable.rawMkString(", ")
      else raw("")) |+|
      (limit match { case (from, to) =>
        raw(" ") |+| emitter.emitLimitClause(from, to)})
    case SqlNaryOp(op, rs) =>
      emitter.emitNaryOp(op, rs)
    case SqlJoin(rs, joinName) =>
      emitter.emitJoin(rs, joinName)
    case SqlJoinOn(r1, r2, ons, joinName) =>
      emitter.emitJoinOn(r1, r2, ons, joinName)
    case SqlExcept(left, unLeft, right, unRight, rheader) =>
      emitter.emitExcept(left, unLeft, right, unRight, rheader)
    case SqlParens(q) => raw("(") |+| q.emitSql |+| ")"
    case FromTable(_, cols) => raw("select distinct ") |+|
      cols.toIndexedSeq.sorted.map {(c: ColumnName) => raw("(") |+| emitter.emitColumnName(c) |+| ")"}.rawMkString(", ") |+|
      " from " |+| this.emitSubquery
    case LiteralSqlTable(nel) => emitter.emitLiteral(nel)
    case _ => sys.error("SQL does not directly support this kind of query: " + this)
  }

  def emitSubquery(implicit emitter: SqlEmitter): RawSql = this match {
    case FromTable(t, _) => emitter.emitTableName(t)
    case _ => raw("(") |+| this.emitSql |+| raw(")")
  }

}

object SqlQuery {
  implicit val SqlQueryShow: Show[SqlQuery] = showA[SqlQuery]
  implicit val SqlQueryEqual: Equal[SqlQuery] = equalA[SqlQuery]
}

case class SqlSelect(options: Set[String] = Set(), // Distinct, all, etc.
                     attrs: Map[SqlColumn, SqlExpr] = Map(), // result attributes
                     tables: Map[TableName, SqlQuery] = Map(), // from clause
                     criteria: List[SqlPredicate] = List(), // where clause
                     groupBy: Map[SqlColumn, SqlExpr] = Map(),
                     orderBy: List[(SqlExpr, SqlOrder)] = List(),
                     // limit clause (where allowed), inclusive 1-indexed (from, to)
                     limit: (Option[Int], Option[Int]) = (None, None)
                   ) extends SqlQuery

case class LiteralSqlTable(lit: NonEmptyList[Map[SqlColumn, SqlExpr]]) extends SqlQuery

sealed abstract class SqlBinOp {
  def emit: RawSql = this match {
    case SqlUnion => "UNION"
    case SqlIntersect => "INTERSECT"
  }
}
case object SqlUnion extends SqlBinOp {
  def apply(r1: SqlQuery, r2: SqlQuery) = (r1, r2) match {
    case (SqlNaryOp(SqlUnion, xs), SqlNaryOp(SqlUnion, ys)) =>
      SqlNaryOp(SqlUnion, xs append ys)
    case (SqlNaryOp(SqlUnion, xs), _) => SqlNaryOp(SqlUnion, xs append NonEmptyList(r2))
    case (_, SqlNaryOp(SqlUnion, ys)) => SqlNaryOp(SqlUnion, r1 <:: ys)
    case _ => SqlNaryOp(SqlUnion, NonEmptyList(r1, r2))
  }
}
case object SqlIntersect extends SqlBinOp {
  def apply(r1: SqlQuery, r2: SqlQuery) = (r1, r2) match {
    case (SqlNaryOp(SqlIntersect, xs), SqlNaryOp(SqlIntersect, ys)) =>
      SqlNaryOp(SqlIntersect, xs append ys)
    case (SqlNaryOp(SqlIntersect, xs), _) => SqlNaryOp(SqlIntersect, xs append NonEmptyList(r2))
    case (_, SqlNaryOp(SqlIntersect, ys)) => SqlNaryOp(SqlIntersect, r1 <:: ys)
    case _ => SqlNaryOp(SqlIntersect, NonEmptyList(r1, r2))
  }
}

// Union relational operator
case class SqlNaryOp(op: SqlBinOp, rs: NonEmptyList[SqlQuery]) extends SqlQuery


// Operator for join, which has different semantics from a binary operator
case class SqlJoin(rs: NonEmptyList[Subquery], joinName: TableName) extends SqlQuery

case class SqlJoinOn(r1: Subquery, r2: Subquery, on: Set[(String, String)], joinName: TableName) extends SqlQuery

// Operator for except, which only exists in some dialects and is worked around in others
case class SqlExcept(left: SqlQuery, unLeft: TableName, right: SqlQuery, unRight: TableName, rheader: Header) extends SqlQuery

// A table with one row but no columns
case object SqlOne extends SqlQuery

// Parentheses in SQL query
case class SqlParens(q: SqlQuery) extends SqlQuery

// select from table.  We assume that `cols` lists every column in
// `table`.
case class FromTable(table: TableName, cols: List[SqlColumn]) extends SqlQuery
