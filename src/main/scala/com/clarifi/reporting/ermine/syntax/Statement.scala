package com.clarifi.reporting.ermine.syntax

import com.clarifi.reporting.Supply
import com.clarifi.reporting.ermine.parsing.Localized
import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Diagnostic._
import com.clarifi.reporting.ermine.Kind.{ subKind }
import com.clarifi.reporting.ermine.Type.{ typeVars, allTypeVars, sub }
import com.clarifi.reporting.ermine.Term.{ termVars }
import scala.collection.immutable.List
import scalaz.Monad
import scalaz.Scalaz._

// misc.
case class ForeignClass(loc: Pos, cls: Class[_]) extends Located
case class ForeignMember(loc: Pos, name: String) extends Located

// body statements
sealed trait Statement extends Located {
  def definedTerms: Set[TermVar] = Set()
  def definedTypes: Set[TypeVar] = Set()
}

sealed trait Explicit {
  def global: Global
  def isType: Boolean
}
case class Single(global: Global, isType: Boolean) extends Explicit
case class Renaming(global: Global, l: Local, isType: Boolean) extends Explicit

object Explicit {
  def lookup(g: Global, l: List[Explicit]): Option[Local] = l collect { case Renaming(n,l,_) if n == g => l} headOption
}

// header statements
// group 1)
case class ImportExportStatement(
  loc: Pos,
  export: Boolean,
  module: String,
  as: Option[String],
  explicits: List[Explicit] = List(),
  using: Boolean = false
) {
  def exported(ty: Boolean, g: Global): Boolean =
    if(using)
      explicits.exists(e => e.global == g && e.isType == ty)
    else
      explicits.forall {
        case Single(global, isType) => g != global || isType != ty
        case _ => true
      }
}

// group 2)
case class FieldStatement(loc: Pos, vs: List[TypeVar], ty: Type) extends Statement {
  override def definedTypes = vs.toSet
}

sealed trait Block extends Statement {
  def statements: List[Statement]
  override def definedTerms = statements.foldLeft(Set():Set[TermVar])(_ ++ _.definedTerms)
  override def definedTypes = statements.foldLeft(Set():Set[TypeVar])(_ ++ _.definedTypes)
}

case class PrivateBlock(loc: Pos, statements: List[Statement]) extends Block
case class DatabaseBlock(loc: Pos, dbName: String, statements: List[Statement]) extends Block
case class ForeignBlock(loc: Pos, statements: List[Statement]) extends Block

sealed trait ForeignStatement extends Statement

sealed trait TypeDef extends Statement {
  def v: TypeVar
  def kindArgs: List[KindVar]
  def typeArgs: List[TypeVar]
  def privateTerms: Set[TermVar] = Set()
  def rho(k: Kind) = typeArgs.foldRight(k)((x,y) => ArrowK(loc.inferred, x.extract, y))
  def asRho(k: Kind): TypeDef
  def closeWith(s: List[TypeVar])(implicit su: Supply): TypeDef
  override def definedTypes = Set(v)
  def close(implicit su: Supply) = closeWith(List())
}

case class ClassBlock(
  loc: Pos,
  v: TypeVar,
  kindArgs: List[KindVar],
  typeArgs: List[TypeVar],
  ctx: List[Type],
  override val privateTerms: Set[TermVar],
  statements: List[BindingStatement]
) extends Block with TypeDef {
  def asRho(k: Kind) = ClassBlock(loc, v as rho(k), kindArgs, typeArgs, ctx, privateTerms, statements)
  override def definedTypes = Set(v)
  def closeWith(s: List[TypeVar])(implicit su: Supply) = {
    val sp = v :: typeArgs ++ s
    ClassBlock(loc, v, kindArgs, typeArgs, ctx.map(_.closeWith(sp)), privateTerms,
      statements.map { case SigStatement(l,vs,t) => SigStatement(l, vs, t.closeWith(sp))
                       case t => t
      }
    )
  }
}

// group 3)
// type foo args = body
case class TypeStatement(loc: Pos, v: TypeVar, kindArgs: List[KindVar], typeArgs: List[TypeVar], body: Type) extends TypeDef {
  def asRho(k: Kind) = TypeStatement(loc, v as rho(k), kindArgs, typeArgs, body)
  def closeWith(s: List[TypeVar])(implicit su: Supply) = TypeStatement(loc, v, kindArgs, typeArgs, body.closeWith(v :: typeArgs ++ s))
}
// data v args = constructors
case class DataStatement(loc: Pos, v: TypeVar, kindArgs: List[KindVar], typeArgs: List[TypeVar], constructors: List[(List[TypeVar], TermVar, List[Type])]) extends TypeDef {
  override def definedTerms = constructors.map(_._2).toSet
  def asRho(k: Kind) = DataStatement(loc, v as rho(k), kindArgs, typeArgs, constructors)
  def closeWith(s: List[TypeVar])(implicit su: Supply) =
    DataStatement(loc, v, kindArgs, typeArgs, constructors.map { case (es, u, l) => (es, u, l.map(_.closeWith(v :: typeArgs ++ s ++ es))) })
}

object TypeDef {
  // perform strongly connected component analysis to infer better kinds
  def typeDefComponents(xs: List[TypeDef]): List[List[TypeDef]] = {
    val vm = xs.map(b => b.v.id -> b).toMap
    val sccs = SCC.tarjan(vm.keySet.toList) { s => {
      val vars = vm(s) match {
        case DataStatement(_, _, _, typeArgs, cons) =>
          cons.foldLeft(Vars() : TypeVars)((acc, c) => acc ++ (allTypeVars(c._3) -- c._1)) -- typeArgs
        case TypeStatement(_, _, _, typeArgs, body) => allTypeVars(body) -- typeArgs
        case ClassBlock(_, _, _, typeArgs, ctx, _, stmts) => (allTypeVars(ctx) ++ allTypeVars(stmts)) -- typeArgs
      }
      vars.toList.collect { case v if vm.contains(v.id) => v.id }
    }}
    sccs.reverse.map { xs => xs.toList.map(vm(_)) }
  }
}

// foreign data "class" Foo a b c
case class ForeignDataStatement(loc: Pos, v: TypeVar, args: List[TypeVar], cls: ForeignClass) extends ForeignStatement {
  override def definedTypes = Set(v)
}
// group 4)

sealed abstract class ForeignTermDef extends ForeignStatement {
  def v: TermVar
}
// foreign method "member" foo : Type
case class ForeignMethodStatement(loc: Pos, v: TermVar, ty: Type, member: ForeignMember) extends ForeignTermDef {
  override def definedTerms = Set(v)
}
// foreign function "class" "member" foo : Type
case class ForeignFunctionStatement(loc: Pos, v: TermVar, ty: Type, cls: ForeignClass, member: ForeignMember) extends ForeignTermDef {
  override def definedTerms = Set(v)
}
// foreign value "class" "member" Foo : Type
case class ForeignValueStatement(loc: Pos, v: TermVar, ty: Type, cls: ForeignClass, member: ForeignMember) extends ForeignTermDef {
  override def definedTerms = Set(v)
}
// foreign constructor foo : a -> b -> Foo a b c
case class ForeignConstructorStatement(loc: Pos, v: TermVar, ty: Type) extends ForeignTermDef {
  override def definedTerms = Set(v)
}
case class ForeignSubtypeStatement(loc: Pos, v: TermVar, ty: Type) extends ForeignTermDef {
  override def definedTerms = Set(v)
}

// table fully.qualified.name.foo : [Bar, Baz, Quux .. a]
case class TableStatement(loc: Pos, dbName: String, vs: List[(List[Name], TermVar)], ty: Type) extends Statement {
  override def definedTerms = vs.map(_._2).toSet
}

// group 5)
// these can occur inside of a let binding
sealed abstract class BindingStatement extends Statement
case class SigStatement(loc: Pos, vs: List[TermVar], ty: Type) extends BindingStatement {
  override def definedTerms = vs.toSet
}

case class TermStatement(loc: Pos, v: TermVar, pats: List[Pattern], body: Term) extends BindingStatement {
  def binding = ImplicitBinding(loc, v, List(Alt(loc, pats, body)))
  override def definedTerms = Set(v)
}

// TODO: allow these to appear in a let binding group as a BindingStatement. using them in a where is problematic since we never reassociate.
case class FixityStatement(loc: Pos, vs: List[Name], typeLevel: Boolean) extends Statement

object Statement {
  implicit def statementHasTypeVars[A <: Statement]: HasTypeVars[A] = new HasTypeVars[A] {
    def vars(stm: A) = stm match {
      case SigStatement(_, vs, t)                      => typeVars(vs) ++ typeVars(t)
      case TableStatement(_, _, vs, t)                 => typeVars(vs.map(_._2)) ++ typeVars(t)
      case FieldStatement(_, _, ty)                    => typeVars(ty)
      case TermStatement(_, v, pats, body)             => typeVars(v) ++ typeVars(pats) ++ typeVars(body)
      case PrivateBlock(_, ss)                         => typeVars(ss)
      case ForeignBlock(_, ss)                         => typeVars(ss) // :List[Statement])
      case DatabaseBlock(_, _, ss)                     => typeVars(ss)
      case ForeignMethodStatement(_, v, t, _)          => typeVars(v) ++ typeVars(t)
      case ForeignFunctionStatement(_, v, t, _, _)     => typeVars(v) ++ typeVars(t)
      case ForeignValueStatement(_, v, t, _, _)        => typeVars(v) ++ typeVars(t)
      case ForeignConstructorStatement(_, v, t)        => typeVars(v) ++ typeVars(t)
      case ForeignSubtypeStatement(_, v, t)            => typeVars(v) ++ typeVars(t)
      case ClassBlock(_, v, _, typeArgs, ctx, _, body) => (typeVars(ctx) ++ typeVars(body)) -- (v :: typeArgs) //?
      case TypeStatement(_, _, _, typeArgs, body)      => typeVars(body) -- typeArgs
      case DataStatement(_, v, _, typeArgs, cons)      =>
        cons.foldLeft(Vars() : TypeVars)((acc, tup) =>
          acc ++ (typeVars(tup._3) -- tup._1)
        ) -- (v :: typeArgs)
      case r : ForeignDataStatement                    => Vars()
      case f : FixityStatement                         => Vars()
    }
    def allVars(stm: A) = stm match {
      case SigStatement(_, vs, t)                      => allTypeVars(vs) ++ allTypeVars(t)
      case TableStatement(_, _, vs, t)                 => allTypeVars(vs.map(_._2)) ++ allTypeVars(t)
      case FieldStatement(_, _, ty)                    => allTypeVars(ty)
      case TermStatement(_, v, pats, body)             => allTypeVars(v) ++ allTypeVars(pats) ++ allTypeVars(body)
      case PrivateBlock(_, ss)                         => allTypeVars(ss)
      case ForeignBlock(_, ss)                         => allTypeVars(ss) // :List[Statement])
      case DatabaseBlock(_, _, ss)                     => allTypeVars(ss)
      case ForeignMethodStatement(_, v, t, _)          => allTypeVars(v) ++ allTypeVars(t)
      case ForeignFunctionStatement(_, v, t, _, _)     => allTypeVars(v) ++ allTypeVars(t)
      case ForeignValueStatement(_, v, t, _, _)        => allTypeVars(v) ++ allTypeVars(t)
      case ForeignConstructorStatement(_, v, t)        => allTypeVars(v) ++ allTypeVars(t)
      case ForeignSubtypeStatement(_, v, t)            => allTypeVars(v) ++ allTypeVars(t)
      case ClassBlock(_, v, _, typeArgs, ctx, _, body) => (typeVars(ctx) ++ typeVars(body)) -- (v :: typeArgs) //?
      case TypeStatement(_, _, _, typeArgs, body)      => allTypeVars(body) -- typeArgs
      case DataStatement(_, v, _, typeArgs, cons)      =>
        cons.foldLeft(Vars() : TypeVars)((acc, tup) =>
          acc ++ (typeVars(tup._3) -- tup._1)
        ) -- (v :: typeArgs)
      case r : ForeignDataStatement                    => Vars()
      case f : FixityStatement                         => Vars()
    }
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], stm: A) = stm match {
      case SigStatement(l, vs, t) =>
           SigStatement(l, Type.sub(ks, ts, vs), Type.sub(ks, ts, t)).asInstanceOf[A]
      case TableStatement(l, db, vs, t) =>
        TableStatement(l, db, vs.map(_._1).zip(Type.sub(ks, ts, vs.map(_._2))), Type.sub(ks, ts, t)).asInstanceOf[A]
      case FieldStatement(l, vs, ty) =>
           FieldStatement(l, vs, ty.subst(ks, ts)).asInstanceOf[A]
      case TermStatement(l, v, pats, body) =>
           TermStatement(l, Type.sub(ks, ts, v), Type.sub(ks, ts, pats), Type.sub(ks, ts, body)).asInstanceOf[A]
      case PrivateBlock(l, ss) =>
           PrivateBlock(l, Type.sub(ks, ts, ss)).asInstanceOf[A]
      case ForeignBlock(l, ss) =>
           ForeignBlock(l, Type.sub(ks, ts, ss)).asInstanceOf[A]
      case DatabaseBlock(a, b, ss) =>
           DatabaseBlock(a, b, Type.sub(ks, ts, ss)).asInstanceOf[A]
      case ForeignMethodStatement(l, v, t, m) =>
           ForeignMethodStatement(l, Type.sub(ks, ts, v), Type.sub(ks, ts, t), m).asInstanceOf[A]
      case ForeignFunctionStatement(l, v, t, c, m) =>
           ForeignFunctionStatement(l, Type.sub(ks, ts, v), Type.sub(ks, ts, t), c, m).asInstanceOf[A]
      case ForeignValueStatement(l, v, t, c, m) =>
           ForeignValueStatement(l, Type.sub(ks, ts, v), Type.sub(ks, ts, t), c, m).asInstanceOf[A]
      case ForeignConstructorStatement(l, v, t) =>
           ForeignConstructorStatement(l, Type.sub(ks, ts, v), Type.sub(ks, ts, t)).asInstanceOf[A]
      case ForeignSubtypeStatement(l, v, t) =>
           ForeignSubtypeStatement(l, Type.sub(ks, ts, v), Type.sub(ks, ts, t)).asInstanceOf[A]
      case ClassBlock(l, v, kindArgs, typeArgs, ctx, privates, body) =>
           ClassBlock(l, v, kindArgs, subKind(ks, typeArgs), Type.sub(ks, ts, ctx), privates, Type.sub(ks, ts, body)).asInstanceOf[A]
      case TypeStatement(l, v, kindArgs, typeArgs, body) =>
           TypeStatement(l, v, kindArgs, subKind(ks, typeArgs), Type.sub(ks, ts, body)).asInstanceOf[A]
      case DataStatement(l, v, kindArgs, typeArgs, cons) =>
           DataStatement(l, v, kindArgs, subKind(ks, typeArgs),
             cons.map{ case (es, v, l) => (es map (subKind(ks, _)), v, Type.sub(ks, ts, l)) }).asInstanceOf[A]
      case r : ForeignDataStatement => r.asInstanceOf[A]
      case f : FixityStatement      => f.asInstanceOf[A]
    }
  }

  def implicitBindingSpan(
    l: Loc,
    v: TermVar,
    alts: List[Alt],
    ss: List[BindingStatement]
  ): (ImplicitBinding, List[BindingStatement]) = ss match {
    case TermStatement(lp, vp, pats, body) :: ss if v == vp =>
      implicitBindingSpan(l,v, Alt(lp, pats, body) :: alts, ss)
    case _ => (ImplicitBinding(l, v, alts.reverse), ss)
  }

  def gatherBindings(ss: List[BindingStatement], is: List[ImplicitBinding] = List(), sigs: List[SigStatement] = List()): (List[ImplicitBinding], List[SigStatement]) = ss match {
    case TermStatement(l, v, pats, body) :: ss =>
      val (i, xs) = implicitBindingSpan(l, v, List(Alt(l, pats, body)), ss)
      gatherBindings(xs, i :: is, sigs)
    case (s : SigStatement)   :: ss => gatherBindings(ss, is, s :: sigs)
    case List() => (is, sigs)
  }

  def checkBindings[M[+_]:Monad:Diagnostic](
    l: Pos,
    is: List[ImplicitBinding],
    ss: List[SigStatement]): M[Localized[(List[ImplicitBinding], List[ExplicitBinding])]] = {
    val im = is.map(i => i.v -> i).toMap // Map[TermVar,ImplicitBinding]
    val sl = for { s <- ss ; v <- s.vs } yield v -> s // List[(TermVar, SigStatement)]
    // we need to check that the variables we've sigged are distinct.
    for {
      es <- sl.traverse[M,ExplicitBinding] { case (v, s) =>
        for {
          i <- im.get(v) match {
            case Some(i) => i.pure[M]
            case None    => raise[M](s.loc, "missing definition")
          }
        } yield ExplicitBinding(i.loc, i.v, Annot.plain(i.loc, s.ty), i.alts)
      }
      /*
      // Stolen from KindParsers and TypeParsers@125
      n <- // need to figure this out
      id <- // and this
      val l = termNames.member()
      val v = V(l, id, Some(n), Bound, ()) // todo: check this.
      val r = for {old <- gets(l.get(_))
                     _ <- modify(l.set(_, Some(v)))
                  } yield modify(l.set(_, old))
      u <- r
      */
      _ <- Localized((), es.map(_.v.name.get.local)).distinct(l) // check that the explicits are distinct
    } yield Localized( ((im -- es.map(_.v)).values.toList,es)
                     , is.map(_.v.name.get.local)
                     )
  }
}
