package com.clarifi.reporting
package ermine.session

import java.util.concurrent._
import com.clarifi.reporting.ermine.{ Result, Success, Failure, Filtered, Document, Death }
import com.clarifi.reporting.ermine.Document.{ text, vsep }
import scalaz.concurrent.{ Promise, Strategy }
import scalaz.concurrent.Strategy._
import java.util.Date
import scalaz.Scalaz._

case class SessionTask[A](env: SessionEnv, promise: Promise[Either[Death,A]])

object SessionTask {
  def fork[A](p: (SessionEnv, Supply) => A)(implicit s: SessionEnv, vs: Supply): SessionTask[A] = {
    val sp = s.copy
    val vsp = vs.split
    SessionTask(
      sp,
      Promise(
        try { Right(p(sp,vsp)) }
        catch { case r : Death => Left(r) }
      )
    )
  }

  // @throws Death
  def join[A](task: SessionTask[A])(implicit s: SessionEnv): A =
    task.promise.get match {
      case Left(e)  => throw Death(e.error, e)
      case Right(a) =>
        s += task.env
        a
    }

  def joins[A](tasks: List[SessionTask[A]])(implicit s: SessionEnv): List[A] = {
    val (failures, successes) = tasks.map(t => (t.promise.get, t.env)).partition { _._1.isLeft }
    if (failures.isEmpty)
      successes.foldRight(List[A]()) {
        case ((Right(x), sp), xs) =>
          s += sp
          x :: xs
        case _ => sys.error("joins: the impossible happened")
      }
    else {
      val failDocs = failures.collect {
        case (Left(Death(e,_)), _) => e
      }
      throw Death(vsep(failDocs))
    }
  }
}

