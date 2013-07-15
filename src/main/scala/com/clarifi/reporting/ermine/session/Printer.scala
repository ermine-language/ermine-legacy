package com.clarifi.reporting.ermine.session

import System.nanoTime
import java.text.DecimalFormat
import com.clarifi.reporting.ermine.Document
import com.clarifi.reporting.ermine.Document._

abstract class Printer {
  def apply(s: String): Unit
}

object Printer {
  def apply(f: String => Unit) = new Printer {
    def apply(s: String) = f(s)
  }
  def say(msg: String)(implicit con: Printer)     { con(msg) }
  def warn(msg: Document)(implicit con: Printer)  { con(msg + "\n") }
  def info(msg: Document)(implicit con: Printer)  { con(msg + "\n") }
  def sayLn(msg: String)(implicit con: Printer)   { con(msg + "\n") }
  def sayLn(msg: Document)(implicit con: Printer) { con(msg.toString + "\n") }

  def simple = new Printer {
    def apply(s: String) = print(s)
  }

  def ignore = new Printer {
    def apply(s: String) {}
  }

  private val df = new DecimalFormat("0.00")

  def benchmark[A](p: => A)(wut: A => Document)(implicit con: Printer): A = {
    val prior = nanoTime
    val a = p
    val now = nanoTime
    val secs = df.format((now - prior) / 1000000000.0)
    con((wut(a) :+: "(" :: secs :+: "seconds)\n").toString)
    a
  }
}
