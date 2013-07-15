package com.clarifi.reporting.ermine

import scalaz._
import scalaz.Scalaz._

/** Fixity defines the fixity of a name (whether it is prefix, infix, postfix, or an identifier),
  * along with the precedence level and in the case of infix, the associativity
  *
  * @author EAK
  */

sealed abstract class Fixity {
  def prec: Int
  def con: Int
}

case object Idfix extends Fixity {
  def prec = 11
  def con = 1
}

case class Prefix(prec: Int) extends Fixity {
  def con = 2
}

case class Infix(prec: Int, assoc: Assoc) extends Fixity {
  def con = 3
}

case class Postfix(prec: Int) extends Fixity {
  def con = 3 // changed from 4 for shunting yard
}


object InfixR {
  def apply(prec: Int) = Infix(prec, AssocR)
  def unapply(p: Infix): Option[Int] = if (p.assoc == AssocR) Some(p.prec) else None
}

object InfixL {
  def apply(prec: Int) = Infix(prec, AssocL)
  def unapply(p: Infix): Option[Int] = if (p.assoc == AssocL) Some(p.prec) else None
}

object InfixN {
  def apply(prec: Int) = Infix(prec, AssocN)
  def unapply(p: Infix): Option[Int] = if (p.assoc == AssocN) Some(p.prec) else None
}
