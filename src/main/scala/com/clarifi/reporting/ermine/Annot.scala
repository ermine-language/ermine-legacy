package com.clarifi.reporting.ermine

import com.clarifi.reporting.Supply
import com.clarifi.reporting.ermine.Kind.{ zipKinds, kindVars, subKind }
import com.clarifi.reporting.ermine.Type.{ typeVars, allTypeVars }
import scala.collection.immutable.List

/** A type annotation with possible (pseudo)-existential holes
  *
  * @author EAK, DJD
  */

case class Annot(loc: Loc, eksists: List[KindVar], exists: List[V[Kind]], body: Type) extends Located {
  def map(f: Type => Type): Annot = Annot(loc, eksists, exists, f(body))
  def close(implicit su: Supply): Annot = {
    val nbody = body.closeWith(exists).nf
    val dks = (kindVars(exists) ++ kindVars(nbody) -- eksists).toList
    val ndks = refreshList(Bound, loc, dks)
    val km = zipKinds(dks, ndks)
    Annot(loc, eksists ++ ndks, subKind(km, exists), subKind(km, nbody))
  }
  def subst(ks: PartialFunction[V[Unit],Kind], ts: PartialFunction[V[Kind],Type]): Annot =
    Annot(loc, eksists, exists map { v => v map { k => k subst ks } }, body.subst(ks, ts))
}

object Annot {
  val annotAny: Annot = {
    val v = V(Loc.builtin,-1,None,Bound,Star(Loc.builtin))
    Annot(Loc.builtin, List(), List(v), VarT(v))
  }

  def plain(l: Loc, ty: Type): Annot = Annot(l, List(), List(), ty)

  implicit def relocatableAnnot: Relocatable[Annot] = new Relocatable[Annot] {
    def setLoc(a: Annot, l: Loc) = Annot(l, a.eksists, a.exists, a.body)
  }

  implicit def annotHasTypeVars: HasTypeVars[Annot] = new HasTypeVars[Annot] {
    def vars(a: Annot) = typeVars(a.body) -- a.exists
    def allVars(a: Annot) = allTypeVars(a.body) -- a.exists
    def sub(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar, Type], a: Annot): Annot = a.subst(ks, ts)
  }
}
