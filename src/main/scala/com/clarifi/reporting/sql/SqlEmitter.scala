package com.clarifi.reporting.sql

import com.clarifi.reporting._
import com.clarifi.reporting.Reporting._
import com.clarifi.reporting.PrimT._
import com.clarifi.reporting.Hints._
import RawSql._

import scalaz._
import Scalaz._
import java.sql.{PreparedStatement,ResultSet,Types}
import java.util.Date
import java.util.UUID

import scalaz._
import Scalaz._

/**
 * Emitters are responsible for emitting SQL statements/queries in
 * specific dialects.
 *
 * @author JAT, MSP, SMB
 */
abstract class SqlEmitter(aliasParens: Boolean = true) {
  def emitNull: RawSql = "NULL"
  def emitNull(stmt: PreparedStatement, i: Int, t: PrimT): Unit = stmt.setNull(i, sqlTypeId(t))

  /** Convenience for emitting a column name `c` qualified by a table
    * name `t`.  I ''don't'' promise to use this instead of
    * `emitTableName` and `emitColumnName`, so take care.
    */
  def emitQualifiedColumnName(t: TableName, c: String): RawSql =
    emitTableName(t) |+| "." |+| emitColumnName(c)

  def emitTableName(s: TableName): RawSql =
    (s.schema :+ s.name) map raw rawMkString "."
  def emitColumnName(s: String): RawSql = s
  def emitProcedureName(s: String, namespace: List[String]): RawSql =
    emitTableName(TableName(s, namespace))
  // These are not symmetric; unemit operates on java.sql bits, and
  // emit is part of SQL codegen.  But if you implement one, you'd
  // better implement the other.
  def unemitTableName(s: String): TableName = TableName(s)
  // TODO: This looks like a hack to me. Do we need to re-parse emitted SQL? -- Runar
  def unemitColumnName(s: String): String = s

  // boolean output - how to stuff a boolean in a PreparedStatement, and how to
  // output a literal Boolean
  def emitBoolean(stmt: PreparedStatement, i: Int, b: Boolean): Unit

  /**
   * Emits the value to use when selecting a boolean value (such as
   * 'select 1' or 'select true').
   */
  def emitBoolean(b: Boolean): RawSql

  def getBoolean(rs: ResultSet, i: Int): Boolean

  def emitUuid(stmt: PreparedStatement, i: Int, b: UUID): Unit
  def emitUuid(u: UUID): RawSql
  def getUuid(rs: ResultSet, i: Int): UUID

  def isTransactional: Boolean
  def setConstraints(enable: Boolean, t: Iterable[TableName]): List[RawSql]

  /**
   * Used at the end of a SELECT...FROM when the list of tables is empty.
   * Returns the empty string by default.
   */
  def emitFromEmptyTable: RawSql = ""

  /**
   * Emits the CREATE TABLE... command.  The format is:
   * CREATE TABLE <tablename> (
   *   <columnname> <columntype>,
   *   ...
   *   FOREIGN KEY (<columnname>, ...) REFERENCES <foreigntablename> (<foreigncolumn>, ...),
   *   ...
   *   PRIMARY KEY(<col1>, ...)
   * )
   */
  def emitCreateTable(e: SqlCreate): RawSql = {
    val cols = e.hints.sortColumns(e.header.keySet).map((colName) =>
      emitColumnName(colName) |+| " " |+| sqlTypeName(e.header(colName)))

    val r2 = e.hints.foreignKeys.map {
      case (foreignTable, setFK) =>
        setFK.map { setCC => {
          val (localCols, foreignCols) = e.schemaHints.tables(foreignTable).sortColumns(setCC.map(_._2)).
            map(fc => setCC.find(_._2 == fc).get).unzip
          raw("FOREIGN KEY ") |+|
            localCols.map(emitColumnName).rawMkString("(", ", ", ")") |+|
            " REFERENCES " |+| emitTableName(foreignTable) |+|
            foreignCols.map(emitColumnName).rawMkString("(", ", ", ")")
      }}.rawMkString(", ")
    }
    val r3 = e.hints.primaryKey.map((colGroup) =>
      if (!colGroup.isEmpty)
        raw("PRIMARY KEY ") |+| e.hints.sortColumns(colGroup).map(emitColumnName).
          rawMkString("(", ", ", ")")
      else raw("")).filter(x => !x.isEmpty)

    emitCreateTableStmt(e.table) |+| (cols ++ r2 ++ r3).rawMkString(" (\n ", ",\n ", " ) ")
  }

  def emitCreateTableStmt(t: TableName): RawSql = {
    val tempmarker: RawSql = t.scope match {
      case TableName.Persistent => ""
      case TableName.Temporary | TableName.Variable(_) => "TEMPORARY"
    }
    raw("CREATE ") |+| tempmarker |+| " TABLE " |+| emitTableName(t)
  }

  /**
   * Emits the command to create an index.  Default implementation:
   * CREATE INDEX indexName ON [tablename] ( col1, col2, ... colN )
   * Works for SQLite, MySQL, and SQL Server.  Vertica doesn't have indexes.
   */
  def emitCreateIndex(t: TableName, hints: TableHints, indexName: String, cols: ColumnGroup, c: IsCandidateKey): Option[RawSql] =
    Some(raw("create index ") |+| indexName |+| " on " |+| emitTableName(t) |+| " " |+|
         hints.sortColumns(cols).map(emitColumnName).rawMkString(" ( ", ", ", " ) "))

  def emitDropIndex(t: TableName, indexName: String): Option[RawSql] =
    Some(raw("drop index ") |+| indexName |+| " on " |+| emitTableName(t))

  // def ifNotExists(t: TableName, r: List[RawSql]) : RawSql = raw("if object_id(N") |+| emitTableName(t) |+| raw(") is not null") |+| r.rawMkString("\n") |+| raw("go")

  /** A SQL statement yielding a relation with three potential outcomes:
    *
    * 1. No rows, `t` does not exist
    * 2. At least one row, first row has NULL `col`: `t` does not exist
    * 3. At least one row, first row has non-NULL `col`: `t` exists
    *
    * @see [[com.clarifi.reporting.relational.SqlScanner]]`#sequenceSql`
    */
  def checkExists(t: TableName, col: ColumnName) : RawSql

  /**
   * Creates the column names for a create table statement, by default.
   */
  def emitSqlColumns(header: Header): RawSql = {
    import std.iterable._
    header.keys.map(emitColumnName).rawMkString(", ")
  }

  /**
   * Generate an insert statement, using the syntax:
   * INSERT INTO <tablename> ( <col1>, <col2>, ... ) VALUES ( <val1>, <val2>, ... )
   */
  def emitInsert(e: SqlInsert): RawSql =
    (raw("insert into ") |+| emitTableName(e.table)
       // we assume query has naturally sorted col order
       |+| e.targetOrder.sorted.map(emitColumnName).rawMkString("(", ", ", ")")
       |+| " " |+| e.sql.emitSql(this))

  /** Insert the result of executing a stored procedure into the given
    * table. */
  def emitExec(e: SqlExec): RawSql =
    ((e.prep foldMap (p => (p emitSql this) |+| raw(" ; ")))
       |+| (raw("insert into ") |+| emitTableName(e.table)
              |+| e.order.map(emitColumnName).rawMkString("(", ", ", ")")
              |+| raw(" exec ") |+| emitProcedureName(e.proc, e.namespace)
              |+| raw(" ")
              |+| e.args.map(_ fold (emitTableName, _.emitSql(this)))
                        .rawMkString(", ")))

  /**
   * Emits a date value from the given Long.
   */
  def emitDate(d: Date): RawSql = {
    raw("'") |+| formatter.format(d) |+| "'"
  }
  def emitDateAddName: String

  def emitInterval(n: Int, u: TimeUnit): RawSql

  val formatter = {
    val fmt = new java.text.SimpleDateFormat("yyyy-MM-dd")
    fmt setTimeZone util.YMDTriple.ymdPivotTimeZone
    fmt
  }
  def emitDateStatement(stmt: java.sql.PreparedStatement, index: Int, date: Date): Unit =
    stmt.setDate(index, new java.sql.Date(date.getTime))

  /**
   * Emits union to ensure proper grouping of multiple options.
   */
  def emitNaryOp(op: SqlBinOp, rs: NonEmptyList[SqlQuery]): RawSql =
    rs.map(r => raw("select * from ") |+| r.emitSubquery(this))
      .intercalate(raw(" ") |+| op.emit |+| " ")

  /**
   * Emit Sql for a natural inner join.
   */
  def emitJoin(rs: NonEmptyList[Subquery],
                     joinName: TableName): RawSql = {
    val (leftP, rightP) = if (aliasParens) ("(", ")") else ("", "")
    raw("select * from ") |+| (rs.map {
      case (q, t, _) => raw(leftP) |+| q.emitSubquery(this) |+| " " |+| emitTableName(t) |+| rightP
    } intercalate raw(" natural join "))
  }

  /**
   * Emits Sql for an inner join on a specified set of column-pairs.
   * TODO: What is the right behavior when there are duplicate column names?
   *       Previously we would arbitrarily retain the _first_ column with a given name.
   *       But that is definitely wrong.
   */
  def emitJoinOn(r1: Subquery,
                 r2: Subquery,
                 on: Set[(ColumnName, ColumnName)],
                 joinName: TableName): RawSql = {
    val rs: NonEmptyList[Subquery] = NonEmptyList(r1, r2)
    val (leftP, rightP) = if (aliasParens) ("(", ")") else ("", "")
    raw("select ") |+| rs.toSet.flatMap {
      case (q, t, h) => h.keySet.map(emitQualifiedColumnName(t, _))
    }.rawMkString(",") |+|
    " from " |+| (rs.map {
      case (q, t, _) => raw(leftP) |+| q.emitSubquery(this) |+| " " |+| emitTableName(t) |+| rightP
    } intercalate raw(" inner join ")) |+|
    " on (" |+| (on.map {
      case (c1, c2) => emitQualifiedColumnName(r1._2, c1) |+| " = " |+| emitQualifiedColumnName(r2._2, c2)
    } intercalate raw(" and ")) |+| ")"
  }

  /**
   * Emits SQL for an except clause.  Default implementation uses "except".
   * Dialects without "except" will need to override and provide a workaround.
   */
  def emitExcept(left: SqlQuery, unLeft: TableName, right: SqlQuery, unRight: TableName, rheader: Header): RawSql =
    raw("select * from ") |+| left.emitSubquery(this) |+| " except select * from " |+| right.emitSubquery(this)

  /** Emits SQL for a Transact-SQL-style `OVER` clause.  Default
    * implementation is a compatibility workaround; the MS SQL emitter
    * should use `OVER` directly.
    */
  def emitOver(e: SqlExpr, over: List[(SqlExpr, SqlOrder)]): RawSql =
    "TODO I don't yet know how to play %s over %s".
      format (e.emitSql(this), over)

  /** Build a query that chooses a range of rows in `query` by
    * ordering them according to `order` and choosing the rows
    * numbered `from` to `to`, one-indexed and inclusive.
    *
    * For implementations with no support for this, answer `query`.
    */
  def emitLimit(query: SqlQuery, queryHeader: Header, unQuery: TableName,
                from: Option[Int], to: Option[Int],
                order: List[(SqlExpr, SqlOrder)],
                unSurrogate: TableName): SqlQuery = query

  /** Emit a `LIMIT` clause for `SELECT`, if supported. */
  def emitLimitClause(from: Option[Int], to: Option[Int]): RawSql = ""

  /** Emit a literal relation */
  def emitLiteral(n: NonEmptyList[Map[SqlColumn, SqlExpr]]): RawSql =
    SqlNaryOp(SqlUnion, n.map(t => SqlSelect(options = Set("distinct"), attrs = t):SqlQuery)).emitSql(this)

  /**
   * Takes a list of SqlExprs and returns a SqlExpr representing that list
   * concatenated together.  The default implementation uses the infix || operator.
   * Override emitConcat_helper to override this functionality.
   */
  final def emitConcat(terms: List[SqlExpr]): SqlExpr = {
    if (terms.length == 0)
      sys.error("Cannot concat zero items")
    else if (terms.length == 1)
      terms(0)
    else
      emitConcat_helper(terms)
  }

  /**
   * Helper for emitConcat that does the actual work.  The length of the list
   * argument is guaranteed to be at least 2.
   */
  protected def emitConcat_helper(terms: List[SqlExpr]): SqlExpr = {
    val first = BinSqlExpr("||", terms(0), terms(1))
    terms.tail.tail.foldLeft(first)(BinSqlExpr("||", _, _))
  }

  /**
   * Emits the population standard deviation aggregation function.  Default
   * implementation uses STDDEV_POP(arg)
   */
  def emitStddevPop(exp: SqlExpr): SqlExpr =
    FunSqlExpr("STDDEV_POP", List(exp))

  /**
   * Emits the sample standard deviation aggregation function.  Default
   * implementation uses STDDEV_SAMP(arg)
   */
  def emitStddevSamp(un: TableName, col: SqlColumn): SqlExpr = FunSqlExpr("STDDEV_SAMP", List(ColumnSqlExpr(un, col)))

  /**
   * Emits the population variance aggregation function.  Default
   * implementation uses VAR_POP(arg)
   */
  def emitVarPop(exp: SqlExpr): SqlExpr =
    FunSqlExpr("VAR_POP", List(exp))

  /**
   * Emits the sample variance aggregation function.  Default
   * implementation uses VAR_SAMP(arg)
   */
  def emitVarSamp(un: TableName, col: SqlColumn): SqlExpr = FunSqlExpr("VAR_SAMP", List(ColumnSqlExpr(un, col)))

  /**
   * Emits the operator to use for integer division. This operator, for
   * example should give 4/3 = 1 (and not a decimal value).
   *
   * The default implementation returns /.
   */
  def emitIntegerDivisionOp: String = "/"

  /**
   * Mapping from ADT type names to SQL type names
   */
  def sqlTypeName(p: PrimT): RawSql

  /**
   * Mapping from ADT type names to SQL type IDs per java.sql.Types
   */
  def sqlTypeId(p: PrimT): Int

  /** Inverse of `sqlTypeId`; should be forgiving.
    *
    * @param dt JDBC DATA_TYPE.
    * @param tn JDBC TYPE_NAME.
    * @param cs JDBC COLUMN_SIZE. */
  def sqlPrimT(dt: Int, tn: String, cs: Int): Option[PrimT]
}

//////////////////////////////////////////////////////////////////////////////
// Traits for specific behavior overrides

/**
 * Overrides emitFromEmptyTable to return " from dual "
 */
trait EmitFromEmptyTable_FromDual extends SqlEmitter {
  override def emitFromEmptyTable = " from dual "
}

/**
 * Overrides emitSqlColumns to include the types of each column
 */
trait EmitSqlColumns_Typed extends SqlEmitter {
  import std.iterable._
  override def emitSqlColumns(header: Header): RawSql =
    header.toIterable.
      map(t => emitColumnName(t._1) |+| " " |+| sqlTypeName(t._2)).rawMkString(", ")
}

/**
 * Override emitBBin to simply group the binary operations, instead
 * of needing to do a 'select' from them.
 */
trait EmitUnion extends SqlEmitter {
  override def emitNaryOp(op: SqlBinOp, rs: NonEmptyList[SqlQuery]): RawSql =
    rs.map(_.emitSql(this)).rawMkString(" " + op.emit.run + " ")
}

/**
 * Overrides emitJoin to use an inner join, for dialects (MS SQL) without natural join
 */
trait EmitJoin_MsSql extends SqlEmitter {
  override def emitJoin(rs: NonEmptyList[Subquery],
                        joinName: TableName): RawSql = {
    implicit val so = Order[TableName].toScalaOrdering
    val allPairs =
      ((((x: List[Subquery]) => (y: List[Subquery]) => x zip y) |@|
      ((x: List[Subquery]) => x.tails.toList.tail))((x, y) => y flatMap x)).apply(rs.list)
    val allCols = rs.foldLeft(Map[ColumnName, TableName]()) {
      case (m, (_, t, h)) => m ++ h.map(_._1 -> t)
    }.toList.sorted.map {
      case (k, v) => emitQualifiedColumnName(v, k)
    }.rawMkString(", ")
    val ons = allPairs flatMap {
      case ((_, t1, h1), (_, t2, h2)) => {
        val is = h1.keySet intersect h2.keySet
        if (is.isEmpty) None else
          Some(is.map(c => emitQualifiedColumnName(t1, c) |+| " = " |+|
                           emitQualifiedColumnName(t2, c)).rawMkString(" and "))
      }
    }
    raw("select ") |+| allCols |+| " from " |+| (rs.list.map {
      case (q, t, _) => q.emitSubquery(this) |+| " " |+| emitTableName(t)
    }).rawMkString(" , ") |+| " where " |+| (if (ons.isEmpty) "1 = 1" else ons.rawMkString(" and "))
  }
}

/**
 * Overrides except to use the 'except' clause provided by the vendor.
 */
trait EmitExcept_MsSql extends SqlEmitter {
  override def emitExcept(left: SqlQuery, unLeft: TableName, right: SqlQuery, unRight: TableName, rheader: Header): RawSql =
    raw("(") |+| left.emitSql(this) |+| ") except (" |+| right.emitSql(this) |+| ")"
}

/**
 * Overrides emitExcept to use a left join, for dialects where "except" is not supported
 */
trait EmitExcept_AsJoin extends SqlEmitter {
  override def emitExcept(left: SqlQuery, unLeft: TableName, right: SqlQuery, unRight: TableName, rheader: Header): RawSql = {
    if (rheader.isEmpty)
      left.emitSql(this)
    else {
      val colnames = rheader.keySet.map(emitColumnName)
      val on = colnames.map(k => emitTableName(unLeft) |+| "." |+| k |+| " = " |+| emitTableName(unRight) |+| "." |+| k).rawMkString(" and ")
      val r0 = emitQualifiedColumnName(unRight, rheader.keys.head)
      raw("select ") |+| colnames.toList.sorted.map(emitTableName(unLeft) |+| "." |+| _).rawMkString(", ") |+| " from " |+|
              left.emitSubquery(this) |+| " " |+| emitTableName(unLeft) |+| " left join " |+|
              right.emitSubquery(this) |+| " " |+| emitTableName(unRight) |+| " on " |+| on |+|
              " where " |+| r0 |+| " is null"
    }
  }
}

/** MS SQL supports `OVER`, and we can abuse that to do limiting. */
trait EmitLimit_AsRowNumberOver extends SqlEmitter {
  import SqlExpr.columns

  /** Simulate `LIMIT` clauses by wrapping `rc` with `row_number()
    * over (order by …) rownum ''rc'' where rownum <= ''to'' and rownum
    * >= ''from''`, then erasing `rownum`.
    */
  override def emitLimit(rc: SqlQuery, h: Header, un: TableName,
                         from: Option[Int], to: Option[Int],
                         order: List[(SqlExpr, SqlOrder)],
                         un2: TableName): SqlQuery =
    SqlSelect(attrs = columns(h, un2),  // erase "rownum"
              tables = Map(un2 -> SqlSelect(
                tables = Map(un -> rc),
                attrs = (columns(h, un) + // add "rownum"
                         ("rownum" -> OverSqlExpr(FunSqlExpr("row_number", List()),
                                                  order))))),
              criteria = List(to.map(x => SqlLte(ColumnSqlExpr(un2, "rownum"),
                                                LitSqlExpr(SqlInt(x)))),
                              from.map(x => SqlGte(ColumnSqlExpr(un2, "rownum"),
                                                  LitSqlExpr(SqlInt(x))))).flatten)
}

/** MySQL and PostgreSQL support `LIMIT`. */
trait EmitLimit_AsLimit extends SqlEmitter {
  import SqlExpr.columns

  /** Wrap the ''rc'' in a select that duplicates ''h'', reorders the
    * relation, and limits according to ''from'' and ''to''.
    */
  override def emitLimit(rc: SqlQuery, h: Header, un: TableName,
                         from: Option[Int], to: Option[Int],
                         order: List[(SqlExpr, SqlOrder)],
                         un2: TableName): SqlQuery =
    SqlSelect(attrs = columns(h, un), tables = Map(un -> rc),
              // reorder and limit RC
              orderBy = order, limit = (from, to))

  /** Use PostgreSQL's 0-indexed `LIMIT ''length'' OFFSET ''from''`
    * syntax, which is also supported in MySQL.
    */
  override def emitLimitClause(from: Option[Int], to: Option[Int]): RawSql = (from, to) match {
    case (Some(x), Some(y)) => "limit %d offset %d" format (y - x + 1, x - 1)
    case (Some(x), None) => "offset %d" format (x - 1)
    case (None, Some(y)) => "limit %d" format y
    case (None, None) => ""
  }
}

trait EmitOver_UsingOver extends SqlEmitter {
  override def emitOver(e: SqlExpr, over: List[(SqlExpr, SqlOrder)]): RawSql =
    e.emitSql(this) |+| " over (order by " |+|
      over.map(x => x._1.emitSql(this) |+| " "
                   |+| x._2.emitSql).rawMkString(", ") |+| ")"
}

/**
 * Overrides emitConcat to use the + operator instead of the || operator
 */
trait EmitConcat_+ extends SqlEmitter {
  override def emitConcat_helper(terms: List[SqlExpr]): SqlExpr = {
    val first = BinSqlExpr("+", terms(0), terms(1))
    terms.tail.tail.foldLeft(first)(BinSqlExpr("+", _, _))
  }
}

/**
 * Overrides emitConcat to use the CONCAT(arg1, ... argn) function present in MySQL
 */
trait EmitConcat_MySQL extends SqlEmitter {
  override def emitConcat_helper(terms: List[SqlExpr]): SqlExpr = {
    FunSqlExpr("Concat", terms)
  }
}

/** Pretend UUIDS are strings. */
trait EmitUuid_Strings extends SqlEmitter {
  def getUuid(rs: ResultSet, i: Int): UUID = java.util.UUID.fromString(rs.getString(i))
  def emitUuid(u: UUID): RawSql = raw("'") |+| u.toString |+| "'"
  def emitUuid(stmt: PreparedStatement, i: Int, u: UUID): Unit =
    stmt.setString(i, u.toString)
}

/**
 * Overrides the standard deviation and variance (sample and population) aggregation
 * functions for SQL Server.
 */
trait EmitStddevVar_MsSQL extends SqlEmitter {
  override def emitStddevPop(exp: SqlExpr): SqlExpr =
    FunSqlExpr("STDEVP", List(exp))
  override def emitStddevSamp(un: TableName, col: SqlColumn): SqlExpr = FunSqlExpr("STDEV", List(ColumnSqlExpr(un, col)))
  override def emitVarPop(exp: SqlExpr): SqlExpr =
    FunSqlExpr("VARP", List(exp))
  override def emitVarSamp(un: TableName, col: SqlColumn): SqlExpr = FunSqlExpr("VAR", List(ColumnSqlExpr(un, col)))
}

trait EmitName_MsSql extends SqlEmitter {
  override def emitColumnName(s: String): RawSql =
    raw("[") |+| raw(s) |+| raw("]")
  override def emitTableName(s: TableName): RawSql = {
    val name = s.scope match {
      case TableName.Persistent => emitColumnName("" + s.name)
      case TableName.Temporary => emitColumnName("##" + s.name)
      case TableName.Variable(_) => raw("@") |+| s.name
    }
    ((s.schema map emitColumnName) :+ name) rawMkString "."
  }
}

/**
 * Override emitIntegerDivisionOp to return 'div', which is
 * MySQL's integer division operator.
 */
trait EmitIntDivOp_MySQL extends SqlEmitter {
  override def emitIntegerDivisionOp: String = "div"
}

/** An unimplemented #checkExists. */
trait EmitCheckExists_AlwaysFails extends SqlEmitter {
  /** @todo Actually yield true sometimes. */
  def checkExists(t: TableName, col: ColumnName) : RawSql =
    (raw("select (") |+| emitNull |+| ") " |+| emitColumnName(col)
       |+| " " |+| emitFromEmptyTable)
}

//////////////////////////////////////////////////////////////////////////////
// SQL dialect implementations

class SqliteEmitter extends SqlEmitter
    with EmitUuid_Strings with EmitCheckExists_AlwaysFails with EmitLimit_AsLimit {

  def isTransactional: Boolean = true
  def setConstraints(enable: Boolean, t: Iterable[TableName]): List[RawSql] =
     if (enable)
       List("PRAGMA foreign_keys = ON")
     else
       List("PRAGMA foreign_keys = OFF")

  def getBoolean(rs: ResultSet, i: Int): Boolean = rs.getInt(i) != 0
  def emitBoolean(b: Boolean): RawSql = if (b) "1" else "0"
  def emitBoolean(stmt: PreparedStatement, i: Int, b: Boolean): Unit = stmt.setInt(i, if (b) 1 else 0)

  override def emitDate(d: Date): RawSql = d.getTime.toString

  def emitDateAddName = sys.error("todo - sqlite dateadd function")
  def emitInterval(n: Int, u: TimeUnit) =
    sys.error("todo - sqlite dateadd function")

  def sqlTypeId(p: PrimT): Int = p match {
    case StringT(_, _) => Types.VARCHAR
    case UuidT(_) => Types.VARCHAR
    case ByteT(_) => Types.INTEGER
    case ShortT(_) => Types.INTEGER
    case IntT(_) => Types.INTEGER
    case LongT(_) => Types.INTEGER
    case DoubleT(_) => Types.REAL
    case DateT(_) => Types.INTEGER
    case BooleanT(_) => Types.INTEGER
  }

  def sqlTypeName(p: PrimT): RawSql = p match {
    case StringT(_, _)  => "text"
    case UuidT(n)       => "text"
    case ByteT(n)       => "integer"
    case ShortT(n)      => "integer"
    case IntT(n)        => "integer"
    case LongT(n)       => "integer"
    case DoubleT(n)     => "real"
    case DateT(n)       => "integer"
    case BooleanT(n)    => "integer"
  }

  def sqlPrimT(x: Int, tn: String, cs: Int) = SqlEmitter.defaultDecodeType(x)

  // doesn't use the "on <tablename>" part of the command
  //override def emitDropIndex(t: TableName, indexName: String): Option[String] =
  //  Some("drop index " + indexName)
}

class MySqlEmitter(innoDB: Boolean) extends SqlEmitter with EmitFromEmptyTable_FromDual
                                      with EmitSqlColumns_Typed
                                      with EmitExcept_AsJoin
                                      with EmitLimit_AsLimit
                                      with EmitConcat_MySQL
                                      with EmitUnion
                                      with EmitIntDivOp_MySQL
                                      with EmitUuid_Strings {
  override def emitTableName(tn: TableName): RawSql =
    (tn.schema :+ tn.name) map emitColumnName rawMkString "."
  override def emitColumnName(cn: String): RawSql = raw("`") |+| raw(cn) |+| raw("`")

  def isTransactional: Boolean = innoDB
  def setConstraints(enable: Boolean, t: Iterable[TableName]): List[RawSql] =
     if (enable)
       List(raw("SET foreign_key_checks = 1"))
     else
       List(raw("SET foreign_key_checks = 0"))

  def getBoolean(rs: ResultSet, i: Int): Boolean = rs.getInt(i) != 0
  def emitBoolean(b: Boolean): RawSql = if (b) "TRUE" else "FALSE" // these are just aliases for 1 and 0
  def emitBoolean(stmt: PreparedStatement, i: Int, b: Boolean): Unit = stmt.setInt(i, if (b) 1 else 0)

  def emitDateAddName = "date_add"
  def emitInterval(n: Int, u: TimeUnit) =
    raw("interval ") |+| raw(n.toString) |+| raw(" " + u.toString)

  import SqlEmitter.nn

  def sqlTypeName(p: PrimT): RawSql = p match {
    case UuidT(n)     => nn(n,"char(36)")
    case BooleanT(n)  => nn(n,"tinyint(1)")
    case _ => SqlEmitter.fallbackSqlTypeName(p)
  }

  def sqlTypeId(p: PrimT): Int = p match {
    case StringT(_,_) => Types.VARCHAR
    case _ => SqlEmitter.fallbackSqlTypeId(p)
  }

  def sqlPrimT(x: Int, tn: String, cs: Int) = SqlEmitter.defaultDecodeType(x)

  def checkExists(t: TableName, col: ColumnName) : RawSql =
    (raw("select (") |+| emitColumnName("TABLE_NAME")
       |+| ") " |+| emitColumnName(col)
       |+| " from "
       |+| emitTableName(TableName("TABLES", List("INFORMATION_SCHEMA")))
       |+| " where "
       |+| emitColumnName("TABLE_NAME") |+| " = " |+| SqlString(t.name).emitSql(this)
       |+| " and " |+| emitColumnName("TABLE_SCHEMA")
       |+| " = " |+| SqlString(t.schema mkString ".").emitSql(this))
}

class MsSqlEmitter extends SqlEmitter with EmitSqlColumns_Typed
                                      with EmitUnion
                                      with EmitJoin_MsSql
                                      with EmitConcat_+
                                      with EmitExcept_MsSql
                                      with EmitLimit_AsRowNumberOver
                                      with EmitOver_UsingOver
                                      with EmitStddevVar_MsSQL
                                      with EmitUuid_Strings
                                      with EmitName_MsSql {

  def isTransactional: Boolean = true
  def setConstraints(enable: Boolean, t: Iterable[TableName]): List[RawSql] =
    if (enable)
      t.toList.map(raw("ALTER TABLE ") |+| emitTableName(_) |+| " WITH CHECK CHECK CONSTRAINT all")
    else
      t.toList.map(raw("ALTER TABLE ") |+| emitTableName(_) |+| " NOCHECK CONSTRAINT all")

  def getBoolean(rs: ResultSet, i: Int): Boolean = rs.getInt(i) != 0
  def emitBoolean(b: Boolean): RawSql = if (b) "1" else "0"
  def emitBoolean(stmt: PreparedStatement, i: Int, b: Boolean): Unit = stmt.setInt(i, if (b) 1 else 0)
  override def emitDateStatement(stmt: PreparedStatement, index: Int, d: Date): Unit =
    stmt.setDate(index, new java.sql.Date(d.getTime - java.util.TimeZone.getDefault.getRawOffset))

  def sqlTypeName(p: PrimT): RawSql = SqlEmitter.fallbackSqlTypeName(p)
  def sqlTypeId(p: PrimT): Int = SqlEmitter.fallbackSqlTypeId(p)
  def emitDateAddName = "dateadd"
  def emitInterval(n: Int, u: TimeUnit) =
    raw(n.toString) |+| raw(", " + u.toString.toLowerCase)

  def sqlPrimT(x: Int, tn: String, cs: Int) = tn match {
    case "date" | "datetime" => Some(DateT()) // jtds gives x = varchar for dates
    case _ => SqlEmitter.defaultDecodeType(x)
  }

  override def emitCreateTable(s: SqlCreate): RawSql = s.table.scope match {
    case TableName.Variable(typeName) =>
      // we *assume* that `typeName` has the correct rowtype.
      raw("declare ") |+| emitTableName(s.table) |+| raw(" as ") |+| raw(typeName)
    case TableName.Persistent | TableName.Temporary =>
      super.emitCreateTable(s)
  }

  override def emitCreateTableStmt(t: TableName): RawSql =
    raw("CREATE ") |+| " TABLE " |+| emitTableName(t)

  def checkExists(t: TableName, col: ColumnName): RawSql =
    (raw("select object_id(N'") |+| emitTableName(t)
       |+| raw("') ") |+| emitColumnName(col) |+| emitFromEmptyTable)
}


class VerticaSqlEmitter extends SqlEmitter(false) with EmitFromEmptyTable_FromDual
                                           with EmitSqlColumns_Typed
                                           with EmitExcept_AsJoin
                                           with EmitUnion
                                           with EmitUuid_Strings
                                           with EmitCheckExists_AlwaysFails {

  def isTransactional: Boolean = true
  def setConstraints(enable: Boolean, t: Iterable[TableName]): List[RawSql] =
    if (enable)
      List(raw("SELECT REENABLE_DUPLICATE_KEY_ERROR()"))
    else
      List(raw("SELECT DISABLE_DUPLICATE_KEY_ERROR()"))

  def getBoolean(rs: ResultSet, i: Int): Boolean = rs.getBoolean(i)
  def emitBoolean(b: Boolean): RawSql = if (b) "TRUE" else "FALSE"
  def emitBoolean(stmt: PreparedStatement, i: Int, b: Boolean): Unit = stmt.setBoolean(i, b)
  def emitDateAddName = sys.error("todo - vertica dateadd function")
  def emitInterval(n: Int, u: TimeUnit) =
    sys.error("todo - vertica dateadd function")

  import SqlEmitter.nn

  def sqlTypeName(p: PrimT): RawSql = p match {
    case UuidT(n)     => nn(n,"char(36)")
    case BooleanT(n)  => nn(n,"boolean")
    case _ => SqlEmitter.fallbackSqlTypeName(p)
  }

  def sqlTypeId(p: PrimT): Int = SqlEmitter.fallbackSqlTypeId(p)

  def sqlPrimT(x: Int, tn: String, cs: Int) = SqlEmitter.defaultDecodeType(x)

  // Vertica doesn't have indexes
  override def emitCreateIndex(t: TableName, hints: TableHints, indexName: String, cols: ColumnGroup, c: IsCandidateKey): Option[RawSql] = None
  override def emitDropIndex(t: TableName, indexName: String): Option[RawSql] = None
}

class PostgreSqlEmitter extends SqlEmitter(false)
                        with EmitSqlColumns_Typed
                        with EmitLimit_AsLimit
                        with EmitUnion
                        with EmitUuid_Strings
                        with EmitCheckExists_AlwaysFails {
  import SqlEmitter.nn

  private[this] def quoteName(s: String): RawSql =
    "\"%s\"" format (s replaceAllLiterally ("\"", "\"\""))
  override def emitTableName(s: TableName) =
    (s.schema :+ s.name) map quoteName rawMkString "."
  override def emitColumnName(s: String) = quoteName(s)

  def isTransactional: Boolean = true

  // You can't reliably disable constraints in PG, so don't try.
  def setConstraints(enable: Boolean, t: Iterable[TableName]):
      List[RawSql] = List.empty

  // Postgres has real booleans
  def getBoolean(rs: ResultSet, i: Int): Boolean = rs.getBoolean(i)
  def emitBoolean(b: Boolean): RawSql = if (b) "TRUE" else "FALSE"
  def emitBoolean(stmt: PreparedStatement, i: Int, b: Boolean): Unit = stmt.setBoolean(i, b)
  def emitDateAddName = sys.error("todo - postgres dateadd function")
  def emitInterval(n: Int, u: TimeUnit) =
    sys.error("todo - postgres dateadd function")

  // PG doesn't play fast & loose with string→date coercion
  override def emitDate(d: Date): RawSql =
    raw("date '") |+| formatter.format(d) |+| "'"

  def sqlTypeName(p: PrimT): RawSql = p match {
    // PG has `uuid' but harder to access from JDBC.
    case UuidT(n)    => nn(n,"char(36)")
    case ByteT(n)    => sqlTypeName(ShortT(n)) // nothing smaller than short
    case DoubleT(n)  => nn(n,"double precision")
    case BooleanT(n) => nn(n, "boolean") // But, real booleans!
    case _           => SqlEmitter.fallbackSqlTypeName(p)
  }

  // See `sqlTypeName` for notes.
  def sqlTypeId(p: PrimT): Int = p match {
    case ByteT(n)    => sqlTypeId(ShortT(n))
    case DoubleT(_)  => Types.DOUBLE
    case BooleanT(_) => Types.BOOLEAN
    case _           => SqlEmitter.fallbackSqlTypeId(p)
  }

  def sqlPrimT(x: Int, tn: String, cs: Int) = SqlEmitter.defaultDecodeType(x)
}

object SqlEmitter {

  /** The fallback type decoder.  Use SqlEmitter's instead. */
  private[sql] def defaultDecodeType(x: Int): Option[PrimT] = {
    import java.sql.{Types => T}
    ((_ match {
      case T.BIT | T.BOOLEAN => BooleanT()
      case T.CHAR | T.VARCHAR | T.NCHAR | T.NVARCHAR
         | T.LONGVARCHAR | T.LONGNVARCHAR => StringT(0)
      case T.DATE => DateT()            // TODO date-without-time
      case T.TIME | T.TIMESTAMP => DateT()
      case T.FLOAT | T.DOUBLE | T.REAL | T.DECIMAL => DoubleT()
      case T.BIGINT => LongT()
      case T.INTEGER => IntT()
      case T.SMALLINT => ShortT()
      case T.TINYINT => ByteT()
    }): PartialFunction[Int, PrimT]).lift(x)
  }

  def nn(n: Boolean, s: String): RawSql = if (n) s else (s |+| " not null")

  def fallbackSqlTypeName(p: PrimT): RawSql = p match {
    case StringT(l,n) => nn(n,"varchar(" |+| (if (l == 0) "1000" else l.toString) |+| ")")
    case UuidT(n)     => nn(n,"uniqueidentifier")
    case ByteT(n)     => nn(n,"tinyint")
    case ShortT(n)    => nn(n,"smallint")
    case IntT(n)      => nn(n,"int")
    case LongT(n)     => nn(n,"bigint")
    case DoubleT(n)   => nn(n,"float")
    case DateT(n)     => nn(n,"date")
    case BooleanT(n)  => nn(n,"bit")
  }

  def fallbackSqlTypeId(p: PrimT): Int = p match {
    case StringT(_,_) => Types.VARCHAR
    case UuidT(_) => Types.CHAR
    case ByteT(_) => Types.TINYINT
    case ShortT(_) => Types.SMALLINT
    case IntT(_) => Types.INTEGER
    case LongT(_) => Types.BIGINT
    case DoubleT(_) => Types.FLOAT
    case DateT(_) => Types.DATE
    case BooleanT(_) => Types.BIT
  }

  val sqliteEmitter = new SqliteEmitter
  val mySqlInnoDBEmitter = new MySqlEmitter(true)
  val mySqlEmitter = new MySqlEmitter(false)
  val msSqlEmitter = new MsSqlEmitter

  val msSqlEmitter2005 = new MsSqlEmitter {
    override def sqlTypeName(p: PrimT): RawSql = p match {
      case DateT(n)     => nn(n,"datetime")
      case _ => SqlEmitter.fallbackSqlTypeName(p)
    }
  }
  val verticaSqlEmitter = new VerticaSqlEmitter

  val postgreSqlEmitter = new PostgreSqlEmitter
}
