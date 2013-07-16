package com.clarifi.reporting

package object sql {
  type SqlColumn = String

  type Subquery = (SqlQuery, TableName, Header)

  object SqlType extends scala.Enumeration {
    val String = Value("String")
    val Int = Value("Int")
    val Double = Value("Double")
    val Long = Value("Long")
    val Date = Value("Date")
  }

}

