package com.clarifi.reporting
package sql

import relational._
import backends._

import scalaz._
import Scalaz._

import com.clarifi.machines._

sealed abstract class SqlStatement {
  import RawSql.raw

  def emitSql(implicit emitter: SqlEmitter): RawSql = this match {
    case e : SqlDrop   => raw("drop table ") |+| emitter.emitTableName(e.table)
    case e : SqlCreate => emitter.emitCreateTable(e)
    case e : SqlInsert => emitter.emitInsert(e)
    case e : SqlDelete => raw("delete from ") |+| emitter.emitTableName(e.table) |+| " where " |+| e.where.emitSql
    case e : SqlExec   => emitter emitExec e
    case x => sys.error("Emission not supported for sql statement " + x)
  }
}

case class SqlIfNotExists(table : TableName, stats : List[SqlStatement]) extends SqlStatement

// DDL Data Types
case class SqlDrop(table: TableName) extends SqlStatement
case class SqlCreate(table: TableName,
                     header: Header,
                     hints: TableHints = TableHints.empty,
                     schemaHints: Hints = Hints.empty) extends SqlStatement

// DML Data Types
case class SqlInsert(table: TableName, targetOrder: List[ColumnName], sql: SqlQuery)
     extends SqlStatement
case class SqlDelete(table: TableName, where: SqlExpr) extends SqlStatement
/** Exec a query and insert into a table. */
case class SqlExec(table: TableName, proc: String, namespace: List[String],
                   prep: List[SqlStatement], order: List[ColumnName],
                   args: List[TableName \/ SqlExpr])
     extends SqlStatement
case class SqlLoad(table: TableName, header: Header, stream: DB[Procedure[Id, Record]]) extends SqlStatement
