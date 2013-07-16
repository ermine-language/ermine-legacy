package com.clarifi.reporting.ermine.session

import com.clarifi.reporting.Supply
import com.clarifi.reporting.ermine.session.Session.SourceFile

/**
 * Evaluator for some Ermine code.
 * Runs with prelude already loaded, so loads are reasonably fast.
 */
case class Evaluator(name: String = "<Default Evaluator>") {
  implicit val supply = Supply.create
  val printer = Printer.simple

  // create a base session with prelude loaded so that we don't have to
  // repeat that work for every report that is loaded.
  val baseEnv: SessionEnv = {
    implicit val e : SessionEnv = new SessionEnv
    Lib.preamble
    Session.loadModules(List("Prelude", "Layout"))(e, supply, printer)
    e.loadFile = SourceFile inOrder (e.loadFile, SourceFile filesystem "core/examples")
    e
  }
  // evaluate some ermine code.
  def eval(module:String, expr:String): Either[Exception, com.clarifi.reporting.ermine.Runtime] =
    try Right(Session.evalInContext(module, expr, "<HtmlWriter>")(baseEnv.copy, supply.split, printer))
    catch { case e: Exception => Left(e) }
}
