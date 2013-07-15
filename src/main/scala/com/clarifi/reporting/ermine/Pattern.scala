package com.clarifi.reporting.ermine

import java.util.Date

import Term.{ Env, termVars, subTermEx }
import Document._
import scala.collection.immutable.List
import Pretty.prettyRuntime
import Runtime.Thunk

// you f'd up
case class PatternMatchFailure(loc: Loc, msg: Document, r: Runtime) extends DocException(
  loc.msg("pattern mismatch"),
  loc.report("pattern mismatch:" :+: msg, prettyRuntime(r)).toString
) with Located

// we f'd up
case class PatternMatchPanic(loc: Loc, msg: Document, r: Runtime) extends DocException(
  loc.msg("pattern mismatch"),
  loc.report("pattern mismatch:" :+: msg, prettyRuntime(r)).toString
) with Located

case class ArityMismatch(loc: Loc) extends DocException(
  loc.msg("arity mismatch"),
  loc.report("arity mismatch").toString
) with Located

sealed trait PatternMatchResult {
  def ++(r: PatternMatchResult): PatternMatchResult
}
case object PatternMismatch             extends PatternMatchResult {
  def ++(r: PatternMatchResult) = r match {
    case PatternExplosion(_) => r
    case _                   => this
  }
}
case class PatternMatched(bound: Env)  extends PatternMatchResult {
  def ++(r: PatternMatchResult) = r match {
    case PatternMatched(bnd) => PatternMatched(bound ++ bnd)
    case _ => r
  }
}
case class PatternExplosion(b: Bottom) extends PatternMatchResult {
  def ++(r: PatternMatchResult) = this
}

// it would be nice to just make this a trait so we could use the same constructors as many of the terms
sealed abstract class Pattern extends Located {
  // match this pattern with a fall-through handler
  def apply(r: Runtime): PatternMatchResult
  // match this pattern irrefutably, as a lazy pattern
  def irrefutable(r: Runtime): Env
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]): Pattern
  def vars: Vars[Annot]
  def close: Pattern = this
}

// variable pattern
case class VarP(v: PatternVar) extends Pattern with Variable[Annot] {
  def apply(r: Runtime) = PatternMatched(Map(v.map(_.body) -> r))
  def irrefutable(r: Runtime) = Map(v.map(_.body) -> r)
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = VarP(v.map(_.subst(ks,ts)))
  def vars = Vars(v)
  override def toString = v.toString
}

case class StrictP(loc: Loc, p: Pattern) extends Pattern {
  def apply(r: Runtime) = r.whnf match {
    case b : Bottom => PatternExplosion(b)
    case rp => p(rp)
  }
  def irrefutable(r: Runtime) = p.irrefutable(r)
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = StrictP(loc, p.subst(ks,ts,m))
  def vars = p.vars
  override def toString = "!(" + p.toString + ")"
}

case class LazyP(loc: Loc, p: Pattern) extends Pattern {
  def apply(r: Runtime)       = PatternMatched(p.irrefutable(r))
  def irrefutable(r: Runtime) = p.irrefutable(r)
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]): Pattern = LazyP(loc, p.subst(ks,ts,m))
  def vars = p.vars
  override def toString = "~(" + p.toString + ")"
}

sealed abstract class LitP[+A] extends Pattern {
  def value: A
  def apply(r: Runtime) =
    if (r.extract[A] == value) PatternMatched(Map())
    else PatternMismatch
  def irrefutable(r: Runtime) = Map() // kinda silly
  def vars = Vars()
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = this
  override def toString = value.toString
}

object LitP { def unapply[A](l: LitP[A]) = Some(l.loc, l.value) }
case class LitIntP(loc: Loc, value: Int) extends LitP[Int]
case class LitLongP(loc: Loc, value: Long) extends LitP[Long]
case class LitByteP(loc: Loc, value: Byte) extends LitP[Byte]
case class LitShortP(loc: Loc, value: Short) extends LitP[Short]
case class LitStringP(loc: Loc, value: String) extends LitP[String]
case class LitCharP(loc: Loc, value: Char) extends LitP[Char]
case class LitFloatP(loc: Loc, value: Float) extends LitP[Float]
case class LitDoubleP(loc: Loc, value: Double) extends LitP[Double]
case class LitDateP(loc: Loc, value: Date) extends LitP[Date]

case class WildcardP(loc: Loc) extends Pattern {
  def apply(r: Runtime) = PatternMatched(Map())
  def irrefutable(r: Runtime) = Map()
  def vars = Vars()
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = this
}

/*
case class SigP(loc: Loc, pat: Pattern, annot: Annot) extends Pattern {
  def apply(r: Runtime, orElse: => Runtime)(f: Env => Runtime) = pat(r, orElse)(f)
  def irrefutable(r: Runtime)(f: Env => Runtime): Runtime = pat.irrefutable(r)(f)
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = SigP(loc, pat.subst(ks,ts,m), annot.subst(ks,ts))
  def vars = pat.vars
}
*/

case class ConP(loc: Loc, con: V[Type], pats: List[Pattern]) extends Pattern {
  private def go(t: Type): Option[Type.Con] = t match {
    case AppT(l,_) => go(l)
    case c : Type.Con => Some(c)
    case _ => None
  }
  val primCon: Option[Type.Con] = con.extract match {
    case AppT(AppT(Arrow(_),dom),_) => go(dom)
    case _ => None
  }
  def apply(r: Runtime) = r.whnf match {
    case rp@Data(g, arr) if Some(g) == con.name => Pattern.matches(loc, pats, arr.toList)
    case b: Bottom => PatternExplosion(b)
    case prim@Prim(p) => primCon match {
      case Some(c) if c.decl.isInstance(p) && pats.length == 1 => pats(0)(prim)
      case Some(c) => PatternMismatch
      case None => sys.error(("non primitive constructor" :+: con.toString :+: "matching primitive:" :+: text(p.toString)).toString)

    }
    case e => PatternMismatch
  }
  def irrefutable(r: Runtime): Env = {
    val refuted = Bottom(throw PatternMatchFailure(loc, "refuted irrefutable pattern", r))
    Pattern.matchesIrrefutably(loc, pats,
      pats.zipWithIndex map {
        case (p,i) => Thunk(
          r.whnf match {
            case rp@Data(g, arr) if Some(g) == con.name => Pattern.matches(loc, pats, arr.toList) match {
              case PatternMatched(_) => arr(i)
              case PatternExplosion(b) => b
              case _                   => refuted
            }
            case b: Bottom => b
            case prim@Prim(p) => primCon match {
              case Some(c) if c.decl.isInstance(p) && pats.length == 1 => prim
              case Some(c) => refuted
              case None => sys.error("panic: non primitive constructor " + con + " encountered primitive value " + p)
                           refuted
            }
            case e => refuted
          }
        )
      }
    )
  }
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) =
    ConP(loc, m.lift(con).getOrElse(con.map(_.subst(ks,ts))), pats.map(_.subst(ks,ts,m)))
  def vars = pats.foldLeft(Vars():Vars[Annot]) { (a,b) => a ++ b.vars }
}

case class ProductP(loc: Loc, pats: List[Pattern]) extends Pattern {
  def apply(r: Runtime) = r.whnf match {
    case rp@Arr(arr) => Pattern.matches(loc, pats, arr.toList)
    case b: Bottom => PatternExplosion(b)
    case e => throw PatternMatchPanic(loc, "not a product", r)
  }
  def irrefutable(r: Runtime) = {
    val refuted = Bottom(throw PatternMatchFailure(loc, "refuted irrefutable pattern", r))
    Pattern.matchesIrrefutably(loc, pats,
      pats.zipWithIndex map {
        case (p,i) => Thunk(
          r.whnf match {
            case Arr(arr) => Pattern.matches(loc, pats, arr.toList) match {
              case PatternMatched(_)   => arr(i)
              case PatternExplosion(b) => b
              case _                   => refuted
            }
            case b: Bottom => b
            case e => refuted
          }
        )
      }
    )
  }
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = ProductP(loc, pats.map(_.subst(ks,ts,m)))
  def vars = pats.foldLeft(Vars():Vars[Annot]) { (a,b) => a ++ b.vars }
}

case class AsP(loc: Loc, p1: Pattern, p2: Pattern) extends Pattern {
  def apply(r: Runtime) = p1(r) ++ p2(r)
  def irrefutable(r: Runtime) = p1.irrefutable(r) ++ p2.irrefutable(r)
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]) = AsP(loc, p1.subst(ks,ts,m), p2.subst(ks,ts,m))
  def vars = p1.vars ++ p2.vars
}

object Pattern {
  // expected: ps.length == qs.length
  def matches(loc: Loc, ps: List[Pattern], qs: List[Runtime], acc: PatternMatchResult = PatternMatched(Map())): PatternMatchResult = (ps,qs) match {
    case (p::ps,q::qs) => matches(loc, ps, qs, acc ++ p(q))
    case (List(),List()) => acc
    case _ => throw new ArityMismatch(loc)
  }

  def matchesIrrefutably(loc: Loc, ps: List[Pattern], qs: List[Runtime], acc: Env = Map()): Env = (ps,qs) match {
    case (p::ps,q::qs) => matchesIrrefutably(loc, ps, qs, p.irrefutable(q) ++ acc)
    case (List(),List()) => acc
    case _ => throw new ArityMismatch(loc)
  }

  implicit def patternHasTermVars: HasTermVars[Pattern] = new HasTermVars[Pattern] {
    def vars(tm: Pattern) = tm match {
      case AsP(_,p,q)      => vars(p) ++ vars(q)
      case ConP(_,_,ps)    => termVars(ps)
      case ProductP(_,ps)  => termVars(ps)
      case LazyP(_,p)      => vars(p)
      case _               => Vars()
    }
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], m: PartialFunction[TermVar, TermVar], tm: Pattern): Pattern = tm.subst(ks,ts,m)
  }

  implicit def patternHasTypeVars: HasTypeVars[Pattern] = new HasTypeVars[Pattern] {
    def vars(tm: Pattern) = tm match {
      case AsP(_,p,q)        => vars(p) ++ vars(q)
      case ConP(_,v,ps)      => Type.typeVars(v.extract) ++ ps.map(vars(_)).foldLeft(Vars() : TypeVars)(_ ++ _)
      case ProductP(_, ps)   => ps.map(vars(_)).foldLeft(Vars() : TypeVars)(_ ++ _)
      case LazyP(_,p)        => vars(p)
      case VarP(v)           => Type.typeVars(v.extract)
      case _                 => Vars()
    }
    def allVars(tm: Pattern) = tm match {
      case AsP(_,p,q)        => allVars(p) ++ allVars(q)
      case ConP(_,v,ps)      => Type.allTypeVars(v.extract) ++ ps.map(allVars(_)).foldLeft(Vars() : TypeVars)(_ ++ _)
      case ProductP(_, ps)   => ps.map(allVars(_)).foldLeft(Vars() : TypeVars)(_ ++ _)
      case LazyP(_,p)        => allVars(p)
      case VarP(v)           => Type.allTypeVars(v.extract)
      case _                 => Vars()
    }
    def sub(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar, Type], tm: Pattern): Pattern = tm.subst(ks,ts,Map())
  }
}
