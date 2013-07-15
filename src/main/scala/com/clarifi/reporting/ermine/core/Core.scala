package com.clarifi.reporting.ermine.core

import com.clarifi.reporting.ermine._
import java.util.Date
import scalaz._
import scalaz.Scalaz._
import Runtime.Thunk

class OpenException extends Exception

sealed abstract class Core[+A] extends Monadic[Core,A] with Traversable[A] {
  def flatMap[B](f: A => Core[B]): Core[B]
  def map[B](f: A => B): Core[B]
  def foreach[U](f: A => U): Unit

  def self = this
  implicit def lift[B](v: Core[B]) = v
  def when(b: Boolean): Core[Unit] = if (b) skip else CGoal(())

  // check for unresolved goals
  def close: Option[Core[Nothing]] =
    if (forall(_ => false)) Some(this.asInstanceOf[Core[Nothing]])
    else None
}

object Core {
  type Env = Map[TermVar, Runtime]

  implicit val coreMonad: Monad[Core] = new Monad[Core] {
    def point[A](a : => A) = CGoal(a)
    def bind[A,B](r : Core[A])(f : A => Core[B]) = r flatMap f
  }

  // def evalBinding(b: Binding, env: Env): Runtime = Runtime.accumArgs(b.arity) { evalAlts(b.loc, _, b.alts, env) }

  def evalAlts(loc: Loc, rs: List[Runtime], e: List[CAlt[Runtime]], env: Env): Runtime = e match {
    case CAlt(l,ps,t) :: ep => Pattern.matches(l, ps, rs) match {
      case PatternMatched(delta) => eval(t, env ++ delta)
      case PatternMismatch       => evalAlts(loc, rs, ep, env)
      case PatternExplosion(b)   => b
    }
    case List()             => Bottom(throw new AltException(loc, rs))
  }

  // NB: you can pass a Core[Nothing] to this function!
  def eval(c: Core[Runtime], env: Env): Runtime = c match {
    case CVar(v)           => env.getOrElse(v, v.error("PANIC: Core.eval: unbound variable " + v))
    case CGoal(r)          => r
    case CApp(f,x)         => eval(f,env).apply(Thunk(eval(x,env)))
    case CLam(l, n, b)     => Fun(x => n(x) match {
      case PatternMismatch       => l.error("failed pattern match")
      case PatternMatched(delta) => eval(b, env ++ delta)
      case PatternExplosion(b)   => b
    })
    case CCase(l, e, alts) => evalAlts(l, List(eval(e, env)), alts, env)
    case CEval             => Fun(_.whnfMatch("Core.eval") { case Prim(c : Core[Nothing]) => Core.eval(c, env) })
    case e : Hardcore      => e.eval
    case CLet(bs, b)       => var envp: Env = null
                              envp = env ++ bs.mapValues(b => Thunk(eval(b, envp)))
                              eval(b, envp)
  }
}

case class CGoal[+A](a: A) extends Core[A] {
  def flatMap[B](f: A => Core[B]) = f(a)
  def map[B](f: A => B): Core[B] = CGoal(f(a))
  def foreach[U](f: A => U) { f(a) }
}

case class CApp[+A](e1: Core[A], e2: Core[A]) extends Core[A] {
  def flatMap[B](f: A => Core[B]) = CApp(e1.flatMap(f),e2.flatMap(f))
  def map[B](f: A => B): Core[B] = CApp(e1.map(f),e2.map(f))
  def foreach[U](f: A => U) { e1.foreach(f); e2.foreach(f) }
}

case class CLam[+A](loc: Loc, pat: Pattern, body: Core[A]) extends Core[A] with Located {
  def flatMap[B](f: A => Core[B]) = CLam(loc, pat, body.flatMap(f))
  def map[B](f: A => B): Core[B] = CLam(loc, pat, body.map(f))
  def foreach[U](f: A => U) { body.foreach(f) }
}

case class CAlt[+A](loc: Loc, patterns: List[Pattern], body: Core[A]) extends Located with Traversable[A] {
  def flatMap[B](f: A => Core[B]) = CAlt(loc, patterns, body.flatMap(f))
  def map[B](f: A => B) = CAlt(loc, patterns, body.map[B](f))
  def foreach[U](f: A => U) { body.foreach(f) }
}

case class CCase[+A](loc: Loc, expr: Core[A], alts: List[CAlt[A]]) extends Core[A] with Located {
  def flatMap[B](f: A => Core[B]) = CCase(loc, expr.flatMap(f), alts.map(_.flatMap(f)))
  def map[B](f: A => B) = CCase(loc, expr.map(f), alts.map(_.map(f)))
  def foreach[U](f: A => U) { expr.foreach(f); for (a <- alts) a.foreach(f) }
}

case class CLet[+A](bindings: Map[TermVar,Core[A]], body: Core[A]) extends Core[A] {
  def flatMap[B](f: A => Core[B]) = CLet(bindings.mapValues(_.flatMap(f)), body.flatMap(f))
  def map[B](f: A => B) = CLet(bindings.mapValues(_.map(f)), body.map(f))
  def foreach[U](f: A => U) { for (p <- bindings) p._2.foreach(f); body.foreach(f) }
}

case class CVar(v: TermVar) extends Core[Nothing] with Located {
  def loc = v.loc
  def flatMap[B](f: Nothing => Core[B]) = this
  def map[B](f: Nothing => B) = this
  def foreach[U](f: Nothing => U) {}
}

case object CEval extends Core[Nothing] {
  def flatMap[B](f: Nothing => Core[B]) = this
  def map[B](f: Nothing => B) = this
  def foreach[U](f: Nothing => U) {}
}

sealed class Hardcore(val eval: Runtime) extends Core[Nothing] {
  def flatMap[B](f: Nothing => Core[B]) = this
  def map[B](f: Nothing => B) = this
  def foreach[U](f: Nothing => U) {}
}

case class CInt(value: Int) extends Hardcore(Prim(value))
case class CLong(value: Long) extends Hardcore(Prim(value))
case class CByte(value: Byte) extends Hardcore(Prim(value))
case class CShort(value: Short) extends Hardcore(Prim(value))
case class CString(value: String) extends Hardcore(Prim(value))
case class CChar(value: Char) extends Hardcore(Prim(value))
case class CFloat(value: Float) extends Hardcore(Prim(value))
case class CDouble(value: Double) extends Hardcore(Prim(value))
case class CDate(value: Date) extends Hardcore(Prim(value))
case class CProduct(n: Int) extends Hardcore(Runtime.accumProduct(n))
case class CQuote(c: Core[Nothing]) extends Hardcore(Prim(c))
case object CEmptyRecord extends Hardcore(Rec(Map()))
