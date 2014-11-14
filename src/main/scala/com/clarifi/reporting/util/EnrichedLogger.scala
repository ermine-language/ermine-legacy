package com.clarifi.reporting.util

import org.apache.log4j.Logger

object EnrichedLogger{
  implicit def enrichMyLogger(log:Logger) = new EnrichedLogger(log)
}

class EnrichedLogger(log:Logger) {
  def timed[T](message:String)(f: => T) = {
    val t1 = System.currentTimeMillis
    try f
    finally log.info(message + " took: %ss" format ((System.currentTimeMillis - t1).toDouble / 1000).toString)
  }

  /** Lazy trace message. */
  def ltrace(s: => String): Unit = if (log isTraceEnabled) log trace s
  /** Lazy debug message. */
  def ldebug(s: => String): Unit = if (log isDebugEnabled) log debug s
}
