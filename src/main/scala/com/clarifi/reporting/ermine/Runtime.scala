package com.clarifi.reporting.ermine

import scala.collection.immutable.{ IntMap, List }
import scala.util.control.NonFatal
import scala.Predef.{error => _, _ }
import scalaz.{Success => _, _}
import scalaz.Scalaz._
import sys.error
import com.clarifi.reporting.Reporting._
import com.clarifi.reporting.relational._
import com.clarifi.reporting._

import Type.{True, False}

class FFI[A](e: => A) {
  def eval = e
}

sealed abstract class Runtime {
  def extract[A]: A
  def nf: Runtime = this
  final def whnf: Runtime = Runtime.swhnf(this)
  def apply1(arg: Runtime): Runtime = error("Cannot apply runtime value " + this + " to " + arg)
  def apply(args: Runtime*): Runtime = args.foldLeft(this)(_.apply1(_))
  def err(caller: String): Runtime = error("Panic: unexpected runtime value in " + caller + " - " + whnf)
  def nfMatch(caller: String)(p: PartialFunction[Runtime, Runtime]): Runtime = {
    val myNf = nf
    p.lift(myNf).getOrElse(myNf.err(caller))
  }
  def whnfMatch(caller: String)(p: PartialFunction[Runtime, Runtime]): Runtime = {
    val myWhnf = whnf
    p.lift(myWhnf).getOrElse(myWhnf.err(caller))
  }
  override def toString = Pretty.ppRuntime(this).runAp.toString
}

class Prim(p: Any) extends Runtime {
  def extract[A] = p.asInstanceOf[A]
  override def apply1(arg: Runtime): Runtime = p match {
    case f : Function1[Any,_] => Prim(f(arg.extract[Any]))
    case _ => error("Cannot apply " + this + " to " + arg)
  }
  override def equals(v: Any) = v match {
    case (rv : Runtime) => rv.whnf match {
      case Prim(q) => p == q
      case Box(q) => p == q
      case e : Bottom => e.inspect
      case _       => false
    }
    case _ => false
  }
  override def toString = p.toString
}

object Prim {
  def apply(p: => Any) = try {
    val pForced = p
    if (pForced == null) Runtime.arrUnit
    else pForced match {
      case r: Runtime => r
      case p => new Prim(p)
    }
  } catch { case e: Throwable => Bottom(throw e) }
  def unapply(p: Prim) = Some(p.extract[Any])
}

class Box(p: Any) extends Runtime {
  def extract[A] = p.asInstanceOf[A]
  override def apply1(arg: Runtime): Runtime = p match {
    case f : Function1[Any,_] => Box(f(arg.extract[Any]))
    case _ => error("Cannot apply " + this + " to " + arg)
  }
  override def equals(v: Any) = v match {
    case (rv : Runtime) => rv.whnf match {
      case Box(q) => p == q
      case Prim(q) => p == q
      case e : Bottom => e.inspect
      case _       => false
    }
    case _ => false
  }
  override def toString = p.toString
}

object Box {
  def apply(b: => Any) = try {
    val bForced = b
    if (bForced == null) Runtime.arrUnit
    else bForced match {
      case r: Runtime => r
      case b => new Box(b)
    }
  } catch { case e: Throwable => Bottom(throw e) }
  def unapply(b: Box) = Some(b.extract[Any])
}

/** Relational value */
class Rel(r: Ext[Nothing, Nothing]) extends Runtime {
  def extract[A] = r.asInstanceOf[A]
  override def equals(v: Any) = v match {
    case (rv : Runtime) => rv.whnf match {
      case Rel(s) => r == s
      case e : Bottom => e.inspect
      case _      => false
    }
    case _ => false
  }
}

object Rel {
  def apply(h: => Ext[Nothing, Nothing]) =
    try new Rel(h) catch { case NonFatal(e) => Bottom(throw e) }
  def unapply(r: Rel) = Some(r.extract[Ext[Nothing, Nothing]])
}

case object EmptyRel extends Runtime {
  def extract[A] = this.asInstanceOf[A]
}

case class Arr(arr: Array[Runtime] = Array()) extends Runtime {
  def extract[A] = this.asInstanceOf[A]
  override def nf = Arr(arr.map(_.nf))

  override def equals(v: Any) = v match {
    case (rv : Runtime) => rv.whnf match {
      case Arr(bss)   => Runtime.arrEq(arr, bss)
      case e : Bottom => e.inspect
      case _          => false
    }
    case _ => false
  }
}

case class Data(name: Global, arr: Array[Runtime] = Array()) extends Runtime {
  def extract[A] = this.asInstanceOf[A]
  override def nf       = Data(name, arr.map(_.nf))

  override def equals(v: Any) = v match {
    case (rv : Runtime) => rv.whnf match {
      case Data(nm, bss) => name == nm && Runtime.arrEq(arr, bss)
      case e : Bottom    => e.inspect
      case _             => false
    }
    case _ => false
  }
}

class Bottom(msg: => Nothing) extends Runtime {
  def inspect = msg
  def extract[A] = msg
  def exn: Exception = try msg catch { case e: Exception => e }
  /** @todo SMRC Use NonFatal for this? */
  private[ermine] def thrown: Throwable = try msg catch { case e: Throwable => e }
  override def apply1(r: Runtime) = this
  override def err(caller: String) = this
  override def toString = "Bottom(" + thrown.toString + ")"
  override def equals(v: Any) = inspect
}

object Bottom {
  def apply(f: => Nothing): Bottom = {
    new Bottom(f)
  }
  def unapply(f: Bottom): Option[() => Nothing] = Some(() => f.inspect)
}

class Rec(val t: Map[String, Runtime]) extends Runtime {
  def extract[A] = this.asInstanceOf[A]
  override def nf = Rec(t.map({ case (k, v) => (k, v.nf)}).toMap)

  override def equals(v: Any) = v match {
    case (rv : Runtime) => rv.whnf match {
      case Rec(u)     => t == u
      case e : Bottom => e.inspect
      case _          => false
    }
    case _ => false
  }
}

object Rec {
  def apply(t: => Map[String, Runtime]): Runtime =
    try new Rec(t) catch { case NonFatal(e) => Bottom (throw e) }
  def unapply(t: Rec) = Some(t.t)
}

class Fun(val f: Runtime => Runtime) extends Runtime  {
  def extract[A] = this.asInstanceOf[A]
  override def nf = Fun(e => f(e).nf)
  override def apply1(arg: Runtime) = f(arg)
}
object Fun {
  def apply(f: Runtime => Runtime): Fun = new Fun(f)
  def apply(name: String, pf: PartialFunction[Runtime, Runtime]): Fun = Fun(a => a.whnfMatch(name)(pf))
  def unapply(f: Fun) = Some(f.f)
}

object Runtime {
  val arrUnit = Arr()

  private sealed abstract class ThunkState { def result: Runtime }
  private case object Whitehole extends ThunkState { def result = Bottom(error("infinite loop detected")) }
  private class Unevaluated(e: => Runtime) extends ThunkState { def result = e }
  private case class Evaluated(result: Runtime) extends ThunkState

  class Thunk(e: => Runtime, val update: Boolean) extends Runtime {
    private[Runtime] val latch = new java.util.concurrent.CountDownLatch(1)
    private[Runtime] var state : ThunkState = new Unevaluated(e)
    private[Runtime] val pending = new java.util.concurrent.ConcurrentLinkedQueue[Thread]
    def extract[A] = whnf.extract[A]
    override def nf: Runtime = whnf.nf
    override def apply1(arg: Runtime): Runtime = whnf.apply1(arg)
    override def equals(v: Any) = whnf.equals(v)
  }
  object Thunk {
    def apply(t: => Runtime, update: Boolean = true) = new Thunk(t, update)
    def unapply(t: Thunk) = Some(swhnf(t))
  }

  @annotation.tailrec
  def swhnf(r: Runtime, chain: List[Thunk] = Nil): Runtime = {
    import collection.JavaConversions._
    r match {
      case t : Thunk => t.state match {
        case Evaluated(e) => writeback(e, chain)
        case Whitehole => {
          if (t.pending.isEmpty || !t.pending.exists(_.getId == Thread.currentThread.getId)) {
            t.latch.await
            swhnf(t, chain)
          } else writeback(Whitehole.result, t :: chain)
        }
        case old => {
          if(t.update) {
            t.state = Whitehole
            t.pending add Thread.currentThread
            swhnf(old.result, t :: chain)
          } else { swhnf(old.result, chain) }
        }
      }
      case _         => writeback(r, chain)
    }
  }

  @annotation.tailrec
  private def writeback(answer: Runtime, chain: List[Thunk]): Runtime = chain match {
    case t :: ts =>
      t.state = Evaluated(answer)
      t.pending.clear
      t.latch.countDown
      writeback(answer, ts)
    case Nil => answer
  }

  @annotation.tailrec
  def appl(v: Runtime, stk: List[Runtime]): Runtime = stk match {
    case Nil => v
    case a :: stkp => swhnf(v) match {
      case t : Thunk                   => sys.error("PANIC: whnf returned thunk")
      case b : Bottom                  => b
      case Fun(f)                      => appl(f(a), stkp)
      case Prim(f : Function1[Any, _]) => appl(Prim(f(a.extract)), stkp) // our current behavior
      case Box(f : Function1[Any, _])  => appl(Box(f(a.extract)), stkp)
      case f                           => sys.error("PANIC: Cannot apply runtime value " + f + " to " + a)
    }
  }

  def arrEq[A](l: Array[A], r: Array[A]): Boolean =
    l.length == r.length && ((0 until r.length) forall (i => l(i) == r(i)))
  def fun2(f: (Runtime, Runtime) => Runtime) = Fun(a => Fun(b => f(a,b)))
  def fun2(name: String, pf: PartialFunction[Runtime, PartialFunction[Runtime, Runtime]]) = Fun(name,pf.andThen(Fun(name,_)))

  def fun3(f: (Runtime, Runtime, Runtime) => Runtime) = Fun(a => Fun(b => Fun(c => f(a,b,c))))
  def fun3(name: String, pf: PartialFunction[Runtime, PartialFunction[Runtime, PartialFunction[Runtime, Runtime]]]) =
    Fun(name,pf.andThen(fun2(name,_)))

  def fun4(f: (Runtime, Runtime, Runtime, Runtime) => Runtime) = Fun(a => Fun(b => Fun(c => Fun(d => f(a,b,c,d)))))
  def fun4(name: String, pf: PartialFunction[Runtime, PartialFunction[Runtime, PartialFunction[Runtime, PartialFunction[Runtime, Runtime]]]]) =
    Fun(name,pf.andThen(fun3(name,_)))

  def fun5(f: (Runtime, Runtime, Runtime, Runtime, Runtime) => Runtime) = Fun(a => Fun(b => Fun(c => Fun(d => Fun(e => f(a,b,c,d,e))))))
  def fun5(name: String, pf: PartialFunction[Runtime, PartialFunction[Runtime, PartialFunction[Runtime, PartialFunction[Runtime, PartialFunction[Runtime, Runtime]]]]]) =
    Fun(name,pf.andThen(fun4(name,_)))

  def accumProduct(n: Int, vals: List[Runtime] = List()): Runtime =
    if (n == 0) Arr(vals.reverse.toArray)
    else Fun(v => accumProduct(n - 1, v :: vals))

  def accumArgs(k: Int, xs: List[Runtime] = List())(f: List[Runtime] => Runtime): Runtime =
    if (k == 0) f(xs.reverse)
    else Fun (x => accumArgs(k - 1, x :: xs)(f))

  def withRec[B](f : Map[String, Runtime] => B) : Runtime => B =
    v => v.whnf match {
      case Rec(m) => f(m)
      case x => error("expected record instead of " + x)
    }

  def fieldFun(f: String => Runtime): Runtime = Fun (v =>
    v.nfMatch("field") {
      case Data(Global(_,n,_), _) => f(n)
    })

  def fieldTup(f: (String, PrimT) => Runtime) = Fun (v =>
    v.nfMatch("field") {
      case Data(Global(_,n,_), ts) => f(n, ts(0).extract[PrimT])
    })

  def toPrimExpr(rt: Runtime, nullable: Boolean = false): PrimExpr = rt.nf match {
    case Prim(s: String) => StringExpr(nullable, s) // PrimType.toPrim(s: String)
    case Prim(i: Int) => PrimType.toPrim(i)
    case Prim(d: java.util.Date) => PrimType.toPrim(d)
    case Prim(b: Boolean) => PrimType.toPrim(b)
    case `True` => PrimType.toPrim(true)
    case `False` => PrimType.toPrim(false)
    case Prim(d: Double) => PrimType.toPrim(d)
    case Prim(b: Byte) => PrimType.toPrim(b)
    case Prim(s: Short) => PrimType.toPrim(s)
    case Prim(l: Long) => PrimType.toPrim(l)
    case Prim(u: java.util.UUID) => PrimType.toPrim(u)
    case NullableValue(Right(rt2)) => toPrimExpr(rt2, true).withNull
    case NullableValue(Left(pt)) => NullExpr(pt)
    // may need to add some smarts here to create a NullExpr
    case o => error("Panic: toPrimExpr: Unsupported primitive: " + o)
  }

  def fromPrimExpr(e: PrimExpr): Runtime = {
    val withoutNull = e match {
      case NullExpr(_) => Bottom(throw new RuntimeException("Null encountered for non-nullable column."))
      case BooleanExpr(_, b) => if (b) True else False
      case _           => Prim(e.value)
    }
    if (e.typ.nullable)
      e match {
        case NullExpr(p) => Data(Global("Builtin","Null",Idfix), Array(Prim(p)))
        case _ => Data(Global("Builtin","Some",Idfix), Array(withoutNull))
      }
    else withoutNull
  }

  def accumData(name: Global, vals: List[Runtime], n: Int): Runtime =
    if (n == 0) Data(name, vals.reverse.toArray)
    else Fun(v => accumData(name, v :: vals, n - 1))

  def buildRelation(ts: List[Runtime]): Runtime = ts match {
    case Nil => EmptyRel
    case (_ :: _) => {
      try {
        Rel(ExtRel(SmallLit(ts.map(x => x.nf match {
          case Rec(tup) => tup.map(a => a._1 -> toPrimExpr(a._2))
          case o => error("Panic: buildRelation: Expected a record. Found: " + o)
        }).toNel.get), ""))
      } catch { case NonFatal(e) => Bottom(throw e) }
    }
  }

  def buildMem(ts: List[Runtime]): Runtime = ts match {
    case Nil => EmptyRel
    case (_ :: _) => {
      try {
        Rel(ExtMem(Literal(ts.map(x => x.nf match {
          case Rec(tup) => tup.map(a => a._1 -> toPrimExpr(a._2))
          case o => error("Panic: buildRelation: Expected a record. Found: " + o)
        }).toNel.get)))
      } catch { case NonFatal(e) => Bottom(throw e) }
    }
  }
}

object NullableValue {
  def unapply(rt: Runtime): Option[Either[PrimT,Runtime]] = rt match {
    case Data(Global("Builtin","Null",Idfix), p) => p(0).whnf match {
      case Prim(pt: PrimT) => Some(Left(pt))
      case o => sys.error("Null data constructor contained a non PrimT value: " + o)
    }
    case Data(Global("Builtin","Some",Idfix), p) => Some(Right(p(0))) // TODO: this is actually not in lib, we need to change this to Prelude when it exists
    case _ => None
  }
}
