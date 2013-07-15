package com.clarifi.reporting

import scalaz._
import scalaz.Order._
import scalaz.std.list._
import scalaz.syntax.order._
import scalaz.syntax.monoid._

case class TableName(name: String, schema: List[String] = Nil,
                     scope: TableName.Scope = TableName.Persistent)

object TableName {
  implicit object TableNameOrder extends Order[TableName] {
    def order(x: TableName, y: TableName) =
      (x.name ?|? y.name) |+| (x.schema ?|? y.schema)
  }

  sealed trait Scope
  case object Persistent extends Scope
  case object Temporary extends Scope
  case class Variable(typeName: String) extends Scope
}

