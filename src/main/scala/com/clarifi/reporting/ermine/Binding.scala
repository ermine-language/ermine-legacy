package com.clarifi.reporting
package ermine

import Term.{ subTermEx, termVars }
import HasTermVars._
import scala.collection.immutable.List

case class Alt(loc: Loc, patterns: List[Pattern], body: Term) extends Located {
  def arity = patterns.length
  def vars: TermVars = (termVars(patterns) ++ termVars(body)) -- (for {
    p <- patterns
    v <- p.vars.toList
  } yield v.map(_.body))
  def typeVars: TypeVars = Type.typeVars(patterns) ++ Type.typeVars(body) // NB: does not return in order
  def allTypeVars: TypeVars = Type.allTypeVars(patterns) ++ Type.allTypeVars(body) // NB: does not return in order
  def subst(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar, TermVar]) =
    Alt(loc, subTermEx(ks,ts,m,patterns), subTermEx(ks,ts,m,body))
  def close(implicit supply: Supply) = Alt(loc, patterns.map(_.close), body.close(supply)) // TODO: pattern closing is suspicious
}

object Alt {
  implicit def altHasTermVars: HasTermVars[Alt] = new HasTermVars[Alt] {
    def vars(b: Alt) = b.vars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], b: Alt) =
      b.subst(ks,ts,es)
  }
  implicit def altHasTypeVars: HasTypeVars[Alt] = new HasTypeVars[Alt] {
    def vars(b: Alt) = b.typeVars
    def allVars(b: Alt) = b.allTypeVars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], b: Alt) = b.subst(ks,ts,Map())
  }
}

sealed abstract class Binding extends Located {
  def v: TermVar
  def alts: List[Alt]
  def arity = alts match {
    case List() => 0
    case a :: _ => a.arity
  }
  def subst(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar, TermVar]): Binding
  def vars: TermVars
  def typeVars: TypeVars
  def allTypeVars: TypeVars
  def close(implicit supply: Supply): Binding
  def remember: Option[Int]
}

object Binding {
  implicit def bindingHasTermVars: HasTermVars[Binding] = new HasTermVars[Binding] {
    def vars(b: Binding) = b.vars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], b: Binding) = b.subst(ks,ts,es)
  }
  implicit def bindingHasTypeVars: HasTypeVars[Binding] = new HasTypeVars[Binding] {
    def vars(b: Binding) = b.typeVars
    def allVars(b: Binding) = b.allTypeVars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], b: Binding) = b.subst(ks,ts,Map())
  }
}

case class ExplicitBinding(loc: Loc, v: TermVar, ty: Annot, alts: List[Alt], remember: Option[Int] = None) extends Binding {
  def subst(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar,TermVar]): ExplicitBinding =
    ExplicitBinding(loc, m.lift(v).getOrElse(v.map(_.subst(ks, ts))), ty.subst(ks, ts), alts.map(_.subst(ks,ts,m)))
  def vars = Vars(v) ++ termVars(alts)
  def typeVars = /*Type.typeVars(v) ++ */ Type.typeVars(ty) ++ Type.typeVars(alts)
  def allTypeVars = Type.allTypeVars(ty) ++ Type.allTypeVars(alts)
  def close(implicit supply: Supply) = ExplicitBinding(loc, v, ty.close(supply), alts.map(_.close(supply)))
  def forgetSignature: ImplicitBinding = ImplicitBinding(loc, v, alts, remember)
}

object ExplicitBinding {
  implicit def explicitBindingHasTermVars: HasTermVars[ExplicitBinding] = new HasTermVars[ExplicitBinding] {
    def vars(b: ExplicitBinding) = b.vars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], b: ExplicitBinding) = b.subst(ks,ts,es)
  }
  implicit def explicitBindingHasTypeVars: HasTypeVars[ExplicitBinding] = new HasTypeVars[ExplicitBinding] {
    def vars(b: ExplicitBinding) = b.typeVars
    def allVars(b: ExplicitBinding) = b.allTypeVars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], b: ExplicitBinding) = b.subst(ks,ts,Map())
  }
}

case class ImplicitBinding(loc: Loc, v: TermVar, alts: List[Alt], remember: Option[Int] = None) extends Binding {
  def subst(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar,Type], m: PartialFunction[TermVar, TermVar]): ImplicitBinding =
    ImplicitBinding(loc, m.lift(v).getOrElse(v.map(_.subst(ks, ts))), alts.map(_.subst(ks,ts,m)))
  def vars = Vars(v) ++ termVars(alts)
  def typeVars = /* Type.typeVars(v) ++ */ Type.typeVars(alts)
  def allTypeVars = Type.allTypeVars(alts)
  def close(implicit supply: Supply) = ImplicitBinding(loc, v, alts.map(_.close(supply)))
}

object ImplicitBinding {
  implicit def implicitBindingHasTermVars: HasTermVars[ImplicitBinding] = new HasTermVars[ImplicitBinding] {
    def vars(b: ImplicitBinding) = b.vars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], b: ImplicitBinding) = b.subst(ks,ts,es)
  }
  implicit def implicitBindingHasTypeVars: HasTypeVars[ImplicitBinding] = new HasTypeVars[ImplicitBinding] {
    def vars(b: ImplicitBinding) = b.typeVars
    def allVars(b: ImplicitBinding) = b.allTypeVars
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], b: ImplicitBinding) = b.subst(ks,ts,Map())
  }

  // perform strongly connected component analysis to infer better types
  def implicitBindingComponents(xs: List[ImplicitBinding]): List[List[ImplicitBinding]] = {
    val vm = xs.map(b => b.v.id -> b).toMap
    val sccs = SCC.tarjan(vm.keySet.toList) { i =>
      termVars(vm(i).alts).toList.collect {
        case v if vm.contains(v.id) => v.id
      }
    }
    sccs.reverse.map { xs => xs.toList.map(vm(_)) }
  }

}
