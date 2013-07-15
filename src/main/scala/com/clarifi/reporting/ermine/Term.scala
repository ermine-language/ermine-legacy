package com.clarifi.reporting
package ermine

import java.util.Date

import com.clarifi.reporting.ermine.Type.{ typeVars, sub, typeHasTypeVars }
import com.clarifi.reporting.ermine.Document._
import com.clarifi.reporting.ermine.Pretty.prettyRuntime
import scala.collection.immutable.List
import scalaz.{ Name => _, _ }
import scalaz.Scalaz._
import Show._

// ghc's patError
case class AltException(loc: Loc, runtimes: List[Runtime]) extends DocException(
  loc.msg("match error"),
  loc.report("match error: no match for" :+: fillSep(punctuate("," :: line, runtimes.map(prettyRuntime(_)))))
) with Located

sealed abstract class Term extends Located {
  def getAnnot: Option[Annot] = None
  def isAnnotated: Boolean = false
  def apply(those: Term*): Term = those.foldLeft(this)(App(_, _))
  def close(implicit supply: Supply): Term = this
}
sealed abstract class Lit[+A] extends Term {
  def value: A
  override def toString = value.toString
  def asPattern: LitP[A]
}

object Lit {
  def unapply[A](l: Lit[A]) = Some(l.loc, l.value)
}

case class LitInt(loc: Loc, value: Int) extends Lit[Int] {
  def asPattern = LitIntP(loc, value)
}
case class LitLong(loc: Loc, value: Long) extends Lit[Long] {
  def asPattern = LitLongP(loc, value)
}
case class LitByte(loc: Loc, value: Byte) extends Lit[Byte] {
  def asPattern = LitByteP(loc, value)
}
case class LitShort(loc: Loc, value: Short) extends Lit[Short] {
  def asPattern = LitShortP(loc, value)
}
case class LitString(loc: Loc, value: String) extends Lit[String] {
  def asPattern = LitStringP(loc, value)
}
case class LitChar(loc: Loc, value: Char) extends Lit[Char] {
  def asPattern = LitCharP(loc, value)
}
case class LitFloat(loc: Loc, value: Float) extends Lit[Float] {
  def asPattern = LitFloatP(loc, value)
}
case class LitDouble(loc: Loc, value: Double) extends Lit[Double] {
  def asPattern = LitDoubleP(loc, value)
}
case class LitDate(loc: Loc, value: Date) extends Lit[Date] {
  def asPattern = LitDateP(loc, value)
}

case class EmptyRecord(loc: Loc) extends Term

case class Product(loc: Loc, n: Int) extends Term

case class App(e1: Term, e2: Term) extends Term {
  def loc = e1.loc
  override def toString = "(" + e1.toString + " " + e2.toString + ")"
  override def close(implicit supply: Supply) = App(e1.close, e2.close)
}

case class Sig(loc: Loc, term: Term, annot: Annot) extends Term {
  override def getAnnot = Some(annot)
  override def isAnnotated = true
  override def close(implicit supply: Supply) = Sig(loc, term.close, annot.close)
}

case class Lam(loc: Loc, pat: Pattern, body: Term) extends Term {
  override def close(implicit supply: Supply) = Lam(loc, pat.close, body.close)
}

case class Var(v: TermVar) extends Term with Variable[Type] {
  override def toString = v.toString
}

case class Rigid(e: Term) extends Term {
  override def isAnnotated = true
  override def getAnnot = e.getAnnot
  def loc = e.loc
  override def close(implicit supply: Supply) = Rigid(e.close)
}

case class Case(loc: Loc, expr: Term, alts: List[Alt]) extends Term { // invariant: alts.every(_.arity == 1)
  override def close(implicit supply: Supply) = Case(loc, expr.close, alts.map(_.close))
}

// Invariant: bindings must be a valid processing of implicits and sigs
case class Let(loc: Loc, implicits: List[ImplicitBinding], explicits: List[ExplicitBinding], body: Term) extends Term {
  override def isAnnotated = body.isAnnotated
  override def getAnnot = body.getAnnot
  override def close(implicit supply: Supply) = Let(loc, implicits.map(_.close), explicits.map(_.close), body.close)
  def bound: List[TermVar] = implicits.map(_.v) ++ explicits.map(_.v)
}

case class Hole(loc: Loc) extends Term

case class Remember(id: Int, expr: Term) extends Term {
  override def close(implicit supply: Supply) = Remember(id, expr.close)
  def loc = expr.loc
}

object Term {
  type Env = Map[TermVar,Runtime]

  def extFun(f: Runtime => Runtime) = Fun(f)
  def zipTerms[A](xs: Iterable[A], ks: Iterable[TermVar]): Map[A,TermVar] = xs.zip(ks).toMap

  implicit def relocatableTerm: Relocatable[Term] = new Relocatable[Term] {
    def setLoc(tm: Term, l: Loc) = tm match {
      case Var(v)             => Var(v.copy(loc = l))
      case Product(_,n)       => Product(l,n)
      case App(e1,e2)         => App(setLoc(e1,l),e2)
      case Sig(_,e,t)         => Sig(l,e,t)
      case Rigid(e)           => Rigid(setLoc(e,l))
      case Lam(_,n,b)         => Lam(l,n,b)
      case LitInt(_,i)        => LitInt(l,i)
      case LitByte(_,f)       => LitByte(l,f)
      case LitShort(_,f)      => LitShort(l,f)
      case LitFloat(_,f)      => LitFloat(l,f)
      case LitLong(_,w)       => LitLong(l,w)
      case LitString(_,s)     => LitString(l,s)
      case LitChar(_,c)       => LitChar(l,c)
      case LitDouble(_,d)     => LitDouble(l,d)
      case LitDate(_,d)       => LitDate(l,d)
      case EmptyRecord(_)      => EmptyRecord(l)
      case Case(_,e,alts)     => Case(l,e,alts)
      case Let(_,is,es,e)     => Let(l,is,es,e)
      case Hole(_)            => Hole(l)
      case Remember(i, e)     => Remember(i, setLoc(e, l))
    }
  }
  implicit def TermShow: Show[Term] = showA[Term]

  import Runtime._

  @annotation.tailrec
  def branchAlts(loc: Loc, rs: List[Runtime], bs: List[Alt]): Either[(Env, Term), Bottom] = bs match {
    case Alt(pl, ps, body) :: bsp => Pattern.matches(pl, ps, rs) match {
      case PatternMismatch        => branchAlts(loc, rs, bsp)
      case PatternMatched(delta)  => Left((delta, body))
      case PatternExplosion(b)    => Right(b)
    }
    case Nil => Right(Bottom(throw new AltException(loc, rs)))
  }

  private def caseBranch(loc: Loc, env: Env, tm: Term, bs: List[Alt]) = branchAlts(loc, List(eval(tm, env)), bs)

  def evalBinding(b: Binding, env: => Env): Runtime =
    Runtime.accumArgs(b.arity) {
      branchAlts(b.loc, _, b.alts) match {
        case Left((delta, body)) => Thunk(eval(body, env ++ delta), false)
        case Right(b)            => b
      }
    }

  private def lambda(l: Loc, env: Env, pat: Pattern, body: Term) =
    Fun(v => pat(v) match {
      case PatternMismatch       => Bottom(throw new AltException(l, List(v)))
      case PatternMatched(delta) => eval(body, env ++ delta, Nil)
      case PatternExplosion(b)   => b
    })

  private def evalLater(e: Term, env: Env): Runtime = Thunk(eval(e, env))

  @annotation.tailrec
  def eval(e: Term, env: Env, stk: List[Runtime] = Nil): Runtime = e match {
    case App(f, x)        => eval(f, env, evalLater(x, env) :: stk)
    case Sig(_, a, _)     => eval(a, env, stk)
    case Rigid(a)         => eval(a, env, stk)
    case Product(_, n)    =>
      if(stk.length > n) sys.error("PANIC: over-applied product constructor.")
      else if(stk.length < n) Runtime.appl(accumProduct(n), stk) // temporary, do something better
      else Arr(stk.toArray) // just right
    case EmptyRecord(_)   => Runtime.appl(Rec(Map()), stk)
    case Lit(_, i)        => Runtime.appl(Prim(i), stk)
    case Case(l, e, alts) => caseBranch(l, env, e, alts) match { // cases use stack for evaluating the discriminee
      case Left((delta, body)) => eval(body, env ++ delta, stk)  // but not for evaluating the body
      case Right(b)            => b
    }
    case Let(l, is, es, b) =>
      var envp: Env = null
      envp = env ++ (is ++ es).map(b => b.v -> evalBinding(b, envp))
      eval(b, envp)
    case Lam(l, n, b) => stk match {
      case Nil       => lambda(l, env, n, b)
      case v :: stkp => n(v) match { // saturated lambdas take no stack
        case PatternMismatch       => Bottom(throw new AltException(l, List(v)))
        case PatternMatched(delta) => eval(b, env ++ delta, stkp)
        case PatternExplosion(b)   => b
      }
    }
    case Var(u) => env.get(u) match {
      case Some(v) => Runtime.appl(v, stk)
      case None    => sys.error("PANIC: eval: unbound variable " + u) // let this escape, don't capture it with Bottom
    }
    case Remember(_, e) => eval(e, env, stk)
  }

  implicit def termHasTermVars: HasTermVars[Term] = new HasTermVars[Term] {
    def vars(tm: Term) = tm match {
      case App(f, x)           => vars(f) ++ vars(x)
      case Rigid(a)            => vars(a)
      case Lam(_, p, b)        => vars(b) -- p.vars.map(v => v map { _.body }).toList
      case l@Let(_, is, es, b) => (termVars(is) ++ termVars(es) ++ vars(b)) -- l.bound
      case Case(_, e, alts)    => (vars(e) ++ termVars(alts))
      case Var(v)              => Vars(v)
      case _                   => Vars()
    }
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], ms: PartialFunction[TermVar, TermVar], tm: Term): Term = tm match {
      case App(f, x)           => App(sub(ks, ts, ms, f), sub(ks, ts, ms, x))
      case Rigid(a)            => Rigid(sub(ks, ts, ms, a))
      case Sig(l, a, s)        => Sig(l, sub(ks, ts, ms, a), s.subst(ks, ts))
      case Lam(l, n, e)        => Lam(l, subTermEx(ks, ts, ms, n), sub(ks, ts, ms, e)) // ?? TODO: patterns have term vars too, substitute there
      case Let(l, is, es, b) => Let(l, subTermEx(ks, ts, ms, is), subTermEx(ks, ts, ms, es), sub(ks, ts, ms, b))
      case Case(l, e, alts)    => Case(l, sub(ks, ts, ms, e), alts.map(subTermEx(ks, ts, ms, _)))
      case Var(v)              => ms.lift(v) match {
        case Some(vp) => Var(vp)
        case None     => tm
      }
      case _                   => tm
    }
  }

  implicit def termHasTypeVars: HasTypeVars[Term] = new HasTypeVars[Term] {
    def vars(tm: Term) = tm match {
      case App(f, x)         => vars(f) ++ vars(x)
      case Rigid(x)          => vars(x)
      case Sig(_, b, a)      => vars(b) ++ Type.typeVars(a)
      case Lam(_, p, b)      => Type.typeVars(p) ++ vars(b)
      case Let(_, is, es, b) => Type.typeVars(is) ++ Type.typeVars(es) ++ vars(b) // -- bg.binds
      case Case(_, e, alts)  => vars(e) ++ Type.typeVars(alts)
      case Var(v)            => Vars() // Type.typeVars(v.extract) is wrong because x -> x will break given the free variables in the rhs x
      case _                 => Vars()
    }
    def allVars(tm: Term) = tm match {
      case App(f, x)         => allVars(f) ++ allVars(x)
      case Rigid(x)          => allVars(x)
      case Sig(_, b, a)      => allVars(b) ++ Type.allTypeVars(a)
      case Lam(_, p, b)      => Type.allTypeVars(p) ++ allVars(b)
      case Let(_, is, es, b) => Type.allTypeVars(is) ++ Type.allTypeVars(es) ++ allVars(b) // -- bg.binds
      case Case(_, e, alts)  => allVars(e) ++ Type.allTypeVars(alts)
      case Var(v)            => Vars() // Type.typeVars(v.extract) is wrong because x -> x will break given the free variables in the rhs x
      case _                 => Vars()
    }
    def sub(ks: PartialFunction[KindVar, Kind], ts: PartialFunction[TypeVar, Type], tm: Term): Term = tm match {
      case App(f, x)         => App(sub(ks, ts, f), sub(ks, ts, x))
      case Rigid(x)          => Rigid(sub(ks, ts, x))
      case Sig(l, b, a)      => Sig(l, sub(ks, ts, b), a.subst(ks, ts))
      case Lam(l, p, e)      => Lam(l, Type.sub(ks, ts, p), sub(ks, ts, e))
      case Let(l, is, es, b) => Let(l, Type.sub(ks, ts, is), Type.sub(ks, ts, es), sub(ks, ts, b))
      case Case(l, e, alts)  => Case(l, sub(ks, ts, e), Type.sub(ks, ts, alts))
      case Var(v)            => Var(v map (Type.sub(ks, ts, _)))
      case _                 => tm
    }
  }

  /** Traverse terms in my tree, leaves-first. */
  def postReplace[M[_]: Monad](e: Term)(f: Term => M[Term]): M[Term] = {
    def recAlt(x: Alt): M[Alt] = x match {
      case Alt(l, p, body) => rec(body) map (Alt(l, p, _))
    }
    // scribble out your boilerplate
    def rec(x: Term): M[Term] = (x match {
      case App(tf, tx) => ^(rec(tf), rec(tx))(App)
      case Sig(loc, term, annot) => rec(term) map (Sig(loc, _, annot))
      case Lam(loc, pat, body) => rec(body) map (Lam(loc, pat, _))
      case Rigid(tt) => rec(tt) map Rigid
      case Case(loc, expr, alts) =>
        ^(rec(expr), alts.traverse(recAlt))(Case(loc, _, _))
      case Let(loc, implicits, explicits, body) =>
        (implicits.traverse(im => im.alts traverse recAlt
                                   map (a => im.copy(alts = a)))
         |@| explicits.traverse(ex => ex.alts traverse recAlt
                                       map (a => ex.copy(alts = a)))
         |@| rec(body)) {(im, ex, bd) => Let(loc, im, ex, bd)}
      case Remember(id, expr) => rec(expr) map (Remember(id, _))
      case _: Lit[_] | _: EmptyRecord | _: Product
         | _: Var | _: Hole => x.pure[M]
    }) flatMap f
    rec(e)
  }

  def termVars[A](x: A)(implicit vars: HasTermVars[A]): TermVars = vars.vars(x)
  def subTerm[A](m: PartialFunction[TermVar,TermVar], x: A)(implicit vars: HasTermVars[A]) = vars.sub(Map(), Map(), m, x)
  def subTermEx[A](ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], ms: PartialFunction[TermVar,TermVar], x: A)(implicit vars: HasTermVars[A]) = vars.sub(ks,ts,ms,x)
}

import Term._

abstract class HasTermVars[A] {
  def vars(a: A): TermVars
  def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], ms: PartialFunction[TermVar, TermVar], a: A): A
}

object HasTermVars {
  implicit def mapHasTermVars[K,A](implicit A:HasTermVars[A]): HasTermVars[Map[K,A]] = new HasTermVars[Map[K,A]] {
    def vars(xs: Map[K, A]) = xs.foldRight(Vars():TermVars)((x,ys) => A.vars(x._2) ++ ys)
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], xs: Map[K, A]): Map[K, A] = xs.map(p => (p._1, A.sub(ks, ts, es, p._2)))
  }

  implicit def listHasTermVars[A](implicit A:HasTermVars[A]): HasTermVars[List[A]] = new HasTermVars[List[A]] {
    def vars(xs: List[A]) = xs.foldRight(Vars():TermVars)((x,ys) => A.vars(x) ++ ys)
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], xs: List[A]): List[A] = xs.map(A.sub(ks, ts, es, _))
  }

  implicit def vHasTermVars[K,A](implicit A:HasTermVars[A]): HasTermVars[V[A]] = new HasTermVars[V[A]] {
    def vars(v: V[A]) = A.vars(v.extract)
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], xs: V[A]): V[A] = xs.map(A.sub(ks, ts, es, _))
  }

  implicit def optionHasTermVars[A](implicit A:HasTermVars[A]): HasTermVars[Option[A]] = new HasTermVars[Option[A]] {
    def vars(xs: Option[A]) = xs.map(A.vars(_)).getOrElse(Vars())
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], es: PartialFunction[TermVar,TermVar], xs: Option[A]): Option[A] = xs.map(A.sub(ks,ts,es,_))
  }
}
