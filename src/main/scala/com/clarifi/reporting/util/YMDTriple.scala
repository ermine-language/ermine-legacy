package com.clarifi.reporting
package util

import java.util.{Calendar, Date, GregorianCalendar, TimeZone}

object YMDTriple {
  /** The timezone in which java.util.Dates are assumed to be when
    * converting to SQL dates, which are epoch-free, timezone-free
    * year-month-day triples. */
  val ymdPivotTimeZone: TimeZone = TimeZone getTimeZone "GMT"

  def apply(y: Int, m: Int, d: Int): Date = {
    val c = new GregorianCalendar(ymdPivotTimeZone)
    c.set(Calendar.MILLISECOND, 0)
    c.set(y, m - (1 - Calendar.JANUARY), d, 0, 0, 0)
    c.getTime
  }

  /** Mar 12, 2013 => (2013, 3, 12) */
  def unapply(a: Date): Some[(Int, Int, Int)] = {
    val c = new GregorianCalendar(ymdPivotTimeZone)
    c.setTime(a)
    Some((c get Calendar.YEAR,
          (c get Calendar.MONTH) + (1 - Calendar.JANUARY),
          c get Calendar.DATE))
  }
}
