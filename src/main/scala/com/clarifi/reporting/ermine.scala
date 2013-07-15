package com.clarifi.reporting

import com.clarifi.reporting.ermine.{ Relocatable, Located, Loc }
import scalaz.{ Lens }
import scala.collection.immutable.List
import Lens._

package object ermine {
  def setLoc[T<:Located](t: T, l: Loc)(implicit T:Relocatable[T]) = T.setLoc(t,l)
  def location[T <: Located](implicit T:Relocatable[T]) = lensu[T,Loc]((s, u) => T.setLoc(s, u), _.loc)

  type KindVar = V[Unit]
  type KindVars = Vars[Unit]

  type TypeVar = V[Kind]
  type TypeVars = Vars[Kind]

  type TermVar = V[Type]
  type TermVars = Vars[Type]

  type PatternVar = V[Annot]
  type PatternVars = Vars[Annot]

  def skip[T[+_]](p:Functorial[T,Any]): T[Unit] = p as ()
  def as[T[+_],A](p:Functorial[T,Any], a: A): T[A] = p as a
  def filterMap[T[+_],A,B](p: Filtered[T,A])(f: A => Option[B]): T[B] = p filterMap f
  def many1[T[+_],A](p: Alternating[T,A]): T[List[A]] = p some // can't use some!
  def skipSome[T[+_]](p:Alternating[T,Any]): T[Unit] = p skipSome
  def many[T[+_],A](p: Alternating[T,A]): T[List[A]] = p many
  def skipMany[T[+_]](p:Alternating[T,Any]): T[Unit] = p skipMany
  def manyTill[T[+_],A](p: Alternating[T,A], end: T[Any]) = p manyTill end
  def skipManyTill[T[+_],A](p: Alternating[T,A], end: T[Any]) = p skipManyTill end
  def sepEndBy[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p sepEndBy sep
  def skipSepEndBy[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p skipSepEndBy sep
  def sepEndBy1[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p sepEndBy1 sep
  def skipSepEndBy1[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p skipSepEndBy1 sep
  def sepBy[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p sepBy sep
  def sepBy1[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p sepBy1 sep
  def skipSepBy[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p sepBy sep
  def skipSepBy1[T[+_],A](p: Alternating[T,A], sep: T[Any]) = p sepBy1 sep
  def chainr[T[+_],A](p: Alternating[T,A])(op: T[(A,A) => A]) = p chainr op
  def chainl[T[+_],A](p: Alternating[T,A])(op: T[(A,A) => A]) = p chainl op
  def endBy[T[+_],A](p: Alternating[T,A], end: T[Any]) = p endBy end
  def endBy1[T[+_],A](p: Alternating[T,A], end: T[Any]) = p endBy1 end
  def skipEndBy[T[+_],A](p: Alternating[T,A], end: T[Any]) = p skipEndBy end
  def skipEndBy1[T[+_],A](p: Alternating[T,A], end: T[Any]) = p skipEndBy1 end
  def extract[T[+_],A](w: Comonadic[T,A]): A = w.extract
  def extend[T[+_],A,B](w: Comonadic[T,A])(f: T[A] => B): T[B] = w.extend[B](f)
  def scope[T[+_],A](w: Scoped[T,A], desc: String): T[A] = w scope desc

  def mapAccum_[S,A](g: S, xs: List[A])(f: (S, A) => S): S = xs match {
    case List()  => g
    case a :: as => mapAccum_(f(g,a),as)(f)
  }

  def mapAccum[S,A,B](g: S, xs: List[A])(f: (S, A) => (S, B)): (S, List[B]) = xs match {
    case List() => (g, List())
    case a :: as =>
      val (gp,b) = f(g,a)
      val (gpp,bs) = mapAccum(gp, as)(f)
      (gpp, b :: bs)
  }

  def freshId(implicit su: Supply) = su.fresh
  def fresh[A](l: Loc, name: Option[Name], ty: VarType, a: A)(implicit su: Supply): V[A] =
    V(l, su.fresh, name, ty, a)
  def freshType(kind: Kind)(implicit supply: Supply): V[Kind] =
    V(Loc.builtin, supply.fresh, None, Bound, kind)
  def freshKind(implicit supply: Supply): V[Unit] =
    V(Loc.builtin, supply.fresh, None, Bound, ())

  def refresh[A](ty: VarType, l: Loc, v: V[A])(implicit su: Supply) = fresh(v.loc.instantiatedBy(l), v.name, ty, v.extract)
  def refreshList[A](ty: VarType, l: Loc, vs: List[V[A]])(implicit su: Supply) = vs.map(refresh(ty, l, _))

  def die(d: Document) = throw Death(d)
  // def empty = throw SubstException(None)
}

// vim: set ts=4 sw=4 et:
