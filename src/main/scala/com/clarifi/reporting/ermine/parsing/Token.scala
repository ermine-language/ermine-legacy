package com.clarifi.reporting.ermine.parsing

/** Tokens are returned by the layout parser rather than raw characters
  *
  * @author EAK
  */

sealed abstract class Token

case object VSemi extends Token {
  override def toString = "virtual semicolon"
}
case object VBrace extends Token {
  override def toString = "virtual right brace"
}
case object WhiteSpace extends Token {
  override def toString = "white space"
}
case object Other extends Token {
  override def toString = "other"
}
/*
case object EOF extends Token {
  override def toString = "EOF"
} */
