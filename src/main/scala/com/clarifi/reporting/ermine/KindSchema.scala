package com.clarifi.reporting.ermine

import Kind._

case class KindSchema(loc: Loc, forall: List[V[Unit]], body: Kind) extends Located {
  def map(f: Kind => Kind) = KindSchema(loc, forall, f(body))
  def ->:(that: KindSchema) = {
    val foralls = forall.toSet
    KindSchema(Loc.builtin, forall ++ that.forall.filterNot(forall.contains(_)), body ->: that.body)
  }
  def at(l: Loc) = KindSchema(l, forall, body)
  def subst(m: PartialFunction[V[Unit],Kind]): KindSchema = KindSchema(loc, forall, body.subst(m))
  def vars: Vars[Unit] = body.vars -- forall
  def isMono = forall.isEmpty && body.isMono
  def isClosed = (kindVars(body) -- forall).isEmpty
}

object KindSchema {
  implicit def relocatableKindSchema: Relocatable[KindSchema] = new Relocatable[KindSchema] {
    def setLoc(t: KindSchema, l: Loc) = KindSchema(l, t.forall, t.body)
  }
  implicit def kindSchemaHasKindVars: HasKindVars[KindSchema] = new HasKindVars[KindSchema] {
    def vars(ks: KindSchema) = kindVars(ks.body) -- ks.forall
    def sub(m: PartialFunction[V[Unit], Kind], ks: KindSchema) = KindSchema(ks.loc, ks.forall, ks.body.subst(m))
  }
}
