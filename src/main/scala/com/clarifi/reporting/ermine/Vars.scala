package com.clarifi.reporting.ermine
import scala.collection.immutable.List

import scalaz.Traverse
import scalaz.Applicative

/**
 * Vars is used in the collection of free variables from some variable-containing
 * value. It is designed to avoid duplicates, keep variables in order of appearance
 * and provide for the filtering out of bound variables, all efficiently.
 */
abstract class Vars[+K] extends Traversable[V[K]] { that =>
  def apply[J >: K](s: Set[V[J]], f: V[K] => Unit): Set[V[J]]

  def ![J >: K](s: Set[V[J]]): List[V[K]] = {
    val builder = List.newBuilder[V[K]]
    this(s, builder += _)
    builder.result
  }

  def ++[J >: K](w: Vars[J]): Vars[J] = new Vars[J] {
    def apply[I >: J](s: Set[V[I]], f: V[J] => Unit) = w(that(s,f), f)
  }

  def ::[J >: K](w: V[J]): Vars[J] = Vars(w) ++ that

  def --[J >: K](w: Traversable[V[J]]): Vars[J] = new Vars[J] {
    val t = w.toSet // Set[V[J]]
    def apply[I >: J](s: Set[V[I]], f: V[J] => Unit): Set[V[I]] =
      (that(s ++ t, f) -- t) ++ (t.map(x => x:V[I]) intersect s)
  }

  def foreach[U](f: V[K] => U) = this(Set[V[K]](), { v => f(v); () }) // !@*)#* scala

  /** if you are going to use this over and over again, convert to a Set first! */
  def contains(v: V[Any]) = exists(_ == v)
}

object Vars {
  def apply() = new Vars[Nothing] {
    def apply[J >: Nothing](s: Set[V[J]], f: V[Nothing] => Unit) = s
  }
  def apply[K](v:V[K]) = new Vars[K] {
    def apply[J >: K](s: Set[V[J]], f: V[K] => Unit) =
      if (s(v)) s
      else { f(v); s + v }
  }
  def apply[K](vs: Traversable[V[K]]) = new Vars[K] {
    def apply[J >: K](s: Set[V[J]], f: V[K] => Unit) = {
      vs.foreach(v => if(s(v)) () else f(v))
      s ++ vs
    }
  }
}

/**
 * VarType provides information about what operations may be performed on
 * a variable, or where it appears in terms.
 *
 *  - Free variables are elligible to be unified with expresions of the
 *     appropriate level.
 *  - Each Skolem variable unifies only with itself.
 *  - Bound variables are intended to be used when a variable is quantified,
 *     and should be substituted with other types of variables when that
 *     quantifier is opened.
 *  - Unspecified variables are made up by parsing to fill in necessary missing
 *     information. For instance in 'forall t. ...' the parser will give t an
 *     unspecified variable kind.
 *  - Ambiguous variables are those that appear only in constraints, and thus have
 *     no canonical order of appearance within the type.
 */
sealed abstract class VarType { def ambiguous = false }
case object Free extends VarType
case object Skolem extends VarType // only instantiated during type checking
case object Bound extends VarType
// case object Fake extends VarType
case object Unspecified extends VarType // this wasn't present in the source syntax and probably needs to be solved before continuing
case class Ambiguous(ty: VarType) extends VarType { override def ambiguous = true }

/**
 * The V class underlies the variables at all levels. Fundamentally, this is
 * a wrapper for the integer id, which is expected to be globally unique within
 * a single run of the program (an invariant which is maintained in various
 * other places), and the VarType, explained above. However, variables also
 * carry an optional name for display, and a value of arbitrary type, which is
 * intended to be used to carry typing information for the variable. Thus,
 * V[Type] is a common term variable type, and V[Kind] is used for type variables.
 */
case class V[+A](loc: Loc, id: Int, name: Option[Name], ty : VarType, extract: A) extends Comonadic[V,A] with Located {
  def self = this
  def at(l: Loc) = V(l, id, name, ty, extract)
  def lift[B](v: V[B]) = v
  def extend[B](f: V[A] => B) = V(loc, id, name, ty, f(this))
  override def equals(other: Any) = other match {
    case V(_,oid,_,_,_) => id == oid
    case _ => false
  }
  override def hashCode = id.hashCode
  override def toString = name match {
    case Some(n) => n.toString + "^" + id.toString + (if(ty == Skolem) "S" else "")
    case None => id.toString + (if(ty == Skolem) "S" else "")

  }
}

object V {
  implicit val vComonad: scalaz.Comonad[V] = new scalaz.Comonad[V] {
    def copoint[A](v: V[A]) = v.extract
    def map[A,B](v: V[A])(f: A => B) = v.map(f)
    def cojoin[A](v: V[A]) = V(v.loc,v.id,v.name,v.ty,v)
    def cobind[A,B](v: V[A])(f: V[A] => B) = map(cojoin(v))(f)
  }

  implicit def relocatableV[A]: Relocatable[V[A]] = new Relocatable[V[A]] {
    def setLoc(v: V[A], l: Loc) = v copy (loc = l)
  }

  implicit def traverseV: Traverse[V] = new Traverse[V] {
    def traverseImpl[F[_],A,B](v: V[A])(f: A => F[B])(implicit ap: Applicative[F]) =
      ap.map(f(extract(v)))((b: B) => v as b)
  }
}

trait Variable[+T] extends Located {
  def v: V[T]
  def loc = v.loc
  override def equals(other: Any) = other match {
    case u : Variable[T] => v.equals(u.v)
    case _ => false
  }
  override def hashCode = v.hashCode
}
