package com.clarifi.reporting
package backends

import scala.util.control.NonFatal

import Reporting._
import java.sql._
import scalaz._
import scalaz.Scalaz._

import sql._

object DB {
  private val Log = org.apache.log4j.Logger.getLogger(DB.getClass)

  def transaction[A](action: DB[A]): DB[A] = (c: Connection) => {
    val oldAutoCommit = c.getAutoCommit
    c.setAutoCommit(false)
    try {
      val r = action(c)
      c.commit
      r
    }
    catch { case e: Throwable => { c.rollback; throw e }}
    finally { c.setAutoCommit(oldAutoCommit) }
  }

  def bracket[A,C](before: DB[A], after: (=> A) => DB[_], thing: (=> A) => DB[C]): DB[C] =
    before >>= (a => ensure(thing(a), after(a)))

  def ensure[A](db: DB[A], what: DB[_]): DB[A] =
    c => try { db(c) } finally { what(c) }

  def catchException[A](db : DB[A]) : DB[Either[java.lang.Throwable,A]] = c => try{Right(db(c))} catch {case NonFatal(e) => Left(e)}

  def prepStmt(s: => RawSql): DB[PreparedStatement] =
    c => {
      c.prepareStatement(s.run)
    }

  def closeStmt(s: => PreparedStatement): DB[Unit] =
    c => s.close

  def executeQuery(s: PreparedStatement): DB[ResultSet] =
    c => {
      s.executeQuery
    }

  def executeUpdate(s: PreparedStatement): DB[Unit] =
    c => {
      s.executeUpdate
    }

  def executeBatch(s: PreparedStatement): DB[Unit] =
    c => s.executeBatch

  def executeQuery(s: RawSql): DB[ResultSet] =
    withStmt(s, executeQuery(_))

  def executeUpdate(s: RawSql): DB[Unit] =
    withStmt(s, executeUpdate(_))

  def closeResultSet(rs: => ResultSet): DB[Unit] =
    c => rs.close

  def withStmt[A](s: => RawSql, f: (=> PreparedStatement) => DB[A]): DB[A] =
    bracket[PreparedStatement, A](prepStmt(s), closeStmt(_), f)
    //bracket[PreparedStatement, A]({println(s.run); prepStmt(s)}, closeStmt(_), f)

  def withResultSet[A](s: => RawSql, f: (=> ResultSet) => DB[A]): DB[A] =
    withStmt(s, p => bracket(executeQuery(p), closeResultSet, f))

  /**
   * Iterates over the ResultSet, feeding it input from the 'get' function. The
   * IterV encapsulates the handling of the input (i.e., by collecting them all,
   * or performing some operation to fold the input to a value, etc).
   */
  def enumResultSet[E,A](rs: ResultSet, iter: IterV[E, A], get: ResultSet => E): DB[IterV[E, A]] = {
    c => {
      var cur = iter
      while (rs.next) {
        cur.fold(done = (_,_) => (),
                 cont = k => { cur = k(IterV.El(get(rs))) })
      }
      cur
    }
  }

  def getMetaData(rs: ResultSet): DB[ResultSetMetaData] =
    c => rs.getMetaData

  def next(rs: ResultSet): DB[Boolean] =
    c => rs.next

  /**
   * String -> String -> DB[A] -> A
   * Takes a driver string, a connection string, and produces a DB-algebra
   * for executing database actions.
   */
  def Run(driver: String) = {
    Class.forName(driver)
    (url: String) => new Run[DB] {
      def run[A](a: DB[A]): A = {
        val conn = DriverManager.getConnection(url)
        try {
          val result = a(conn)
          if (Log.isDebugEnabled) Log.debug(result.toString)
          result
        }
        finally { conn.close }
      }
    }
  }

  def RunUser(driver: String) = {
    Class.forName(driver)
    (url: String, user: String, password: String) => new Run[DB] {
      def run[A](a: DB[A]): A = {
        val conn = DriverManager.getConnection(url, user, password)
        try { a(conn) }
        finally { conn.close }
      }
    }
  }

  lazy val sqliteTestDB = Run("org.sqlite.JDBC")("jdbc:sqlite::memory:")

}
