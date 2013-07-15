package com.clarifi.reporting

import scalaz._
import Equal._
import Show._

/** Tag indicating whether a sort happens in ascending or descending
  * order. */
sealed trait SortOrder {
  /** Fold. */
  def apply[Z](asc: => Z, desc: => Z): Z
}

object SortOrder {
  case object Asc extends SortOrder {
    def apply[Z](asc: => Z, desc: => Z): Z = asc
  }

  case object Desc extends SortOrder {
    def apply[Z](asc: => Z, desc: => Z): Z = desc
  }

  implicit val SortOrderEqual: Equal[SortOrder] = equalA
  implicit val SortOrderShow: Show[SortOrder] = showFromToString
}

