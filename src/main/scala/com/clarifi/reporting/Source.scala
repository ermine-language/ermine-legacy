package com.clarifi.reporting

import scalaz._
import Show._
import Equal._
import Scalaz._

case class Source(source: String = "", namespace: List[String] = List())

object Source {
  implicit def sourceEq: Equal[Source] = implicitly[Equal[(List[String], String)]] contramap {
    x => (x.namespace, x.source)
  }

  implicit def sourceShow: Show[Source] = new Show[Source] {
    override def show(s: Source) = Cord(s.toString)
  }
}


