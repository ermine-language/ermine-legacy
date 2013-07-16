package com.clarifi.reporting
package backends

import java.sql.Connection

import com.clarifi.reporting.relational._
import com.clarifi.reporting.backends._
import com.clarifi.reporting.sql.SqlEmitter

object Scanners {
  def StateScanner           = new StateScanner
  def MySQLInnoDB            = new SqlScanner()(SqlEmitter.mySqlInnoDBEmitter)
  def MySQL                  = new SqlScanner()(SqlEmitter.mySqlEmitter)
  def Postgres               = new SqlScanner()(SqlEmitter.postgreSqlEmitter)
  def Vertica                = new SqlScanner()(SqlEmitter.verticaSqlEmitter)
  def SQLite                 = new SqlScanner()(SqlEmitter.sqliteEmitter)
  /** Pre 2008, SQL server did not have a separate date type, only datetime. */
  def MicrosoftSQLServer2005 = new SqlScanner()(SqlEmitter.msSqlEmitter2005)
  def MicrosoftSQLServer     = new SqlScanner()(SqlEmitter.msSqlEmitter)
}

object Runners {
  def MySQL(url: String): Run[DB]              = DB.Run("org.gjt.mm.mysql.Driver")(url)
  def MicrosoftSQLServer(url: String): Run[DB] = DB.Run("net.sourceforge.jtds.jdbc.Driver")(url)
  def Vertica(url: String): Run[DB]            = DB.Run("com.vertica.Driver")(url)
  def SQLite(url: String): Run[DB]             = DB.Run("org.sqlite.JDBC")(url)
  def Postgres(url: String): Run[DB]           = DB.Run("org.postgresql.Driver")(url)
  def liteDB: Run[DB] = DB.sqliteTestDB

  def fromConnection(conn: Connection): Run[DB] = new Run[DB] {
    def run[A](a: DB[A]): A = try a(conn) finally { conn.close }
  }
}
