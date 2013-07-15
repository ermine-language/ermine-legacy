package com.clarifi.reporting
package ermine

import com.clarifi.reporting.{ PrimT }
import com.clarifi.reporting.ermine.Document.{ ordinal, text }
import com.clarifi.reporting.ermine.Relocatable.{ preserveLoc }
import scala.collection.Iterable
import scalaz.{ Show, Equal }
import scalaz.Scalaz._
import scala.collection.immutable.List
import java.util.Date
import Kind._
import Type._
import Equal._
import Show._

import scala.reflect._

/** Types
 *
 * @author EAK
 */

sealed abstract class Type extends Located {
  def map(f: Kind => Kind): Type = this
  /**
   * Fixes up a type to comply with the various invariants we
   * expect of them.
   *
   * This also expands all aliases.
   */
  def nf(implicit supply: Supply): Type = nfWith(List())
  /**
   * The internal implementation of nf, which keeps track of a stack
   * of types that the type in question is applied to.
   */
  def nfWith(stk: List[Type])(implicit su: Supply): Type = stk.foldLeft(this)(AppT(_,_))
  /**
   * The Java/Scala class that the type corresponds to for the
   * purposes of FFI marshalling.
   */
  def foreignLookup: Class[_] = implicitly[ClassTag[AnyRef]].runtimeClass
  def unboxedForeign: Boolean = false
  /**
   * A convenience function that allows us to write
   *   f(x,y,z)
   * instead of
   *   AppT(AppT(AppT(f,x),y)z)
   */
  def apply(those: Type*): Type = those.foldLeft(this)(AppT(_, _))
  def =>:(t:       (Type,List[Type])) : Type = Forall(Loc.builtin, List(), List(), Exists(Loc.builtin, List(), List(       Part(Loc.builtin,t._1,t._2))), this)
  def =>:(ts: List[(Type,List[Type])]): Type = Forall(Loc.builtin, List(), List(), Exists(Loc.builtin, List(), ts.map(t => Part(Loc.builtin,t._1,t._2))), this)
  def =>:(t: Type): Type = Forall(Loc.builtin, List(), List(), t, this)
  def ->:(that: Type): Type = Arrow(Loc.builtin, that, this)
  def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type]): Type = this
  def mono: Boolean = true
  def isTrivialConstraint: Boolean = false
  def hasRowConstraints: Boolean = rowConstraints nonEmpty
  def rowConstraints: List[Type] = List()
  def isClassConstraint: Boolean = false
  def ++(t: Type) = Exists.mk(loc orElse t.loc, List(), List(this, t))
  def at(l: Loc): Type

  // TODO: actually close the type!
  /**
   * Looks through the type for unquantified variables and quantifies
   * them. This specifically ignores variables with capitalized names,
   * as we have determined that auto-quantifying those covers up
   * what should be unbound constructor errors frequently (due to our
   * mostly adhering to a Haskell-like naming convention).
   */
  def close(implicit supply: Supply): Type = closeWith(List()).nf
  /**
   * The internal implementation of close; takes a list of additional
   * variables to not be quantified.
   */
  def closeWith(vs: List[TypeVar])(implicit supply: Supply): Type = {
    val rvs = (typeVars(this) -- vs).toList.filter {
      v => !v.name.isDefined || v.name.get.string.charAt(0).isLower
    }
    if (rvs.isEmpty) this
    else Forall.mk(loc, List(), rvs, Exists(loc.inferred), this)
  }
  /**
   * Refreshes the quantified variables using the given supply, to maintain
   * the Barendregt convention in the face of subsitution.
   */
  def barendregtAlpha(implicit supply: Supply): Type = this

  /**
   * Replaces any Memory constructors with the body of the Memory
   */
  def forget: Type = this
}

/**
 * ConDecls represent various information about the way a type
 * constructor was declared, and the consequences thereof. It
 * is an open trait so that the subtypes that contain specific
 * information can appear near where that information is actually
 * used. A minimal interface that is necessary for all ConDecls
 * is of course specified.
 */
trait ConDecl {
  /**
   * This is the Class that is expected to correspond to the Con's
   * type in Scala. It is used when looking up foreign functions
   * and the like.
   */
  def foreignLookup: Class[_] = implicitly[ClassTag[AnyRef]].runtimeClass
  def unboxedForeign: Boolean = false
  /**
   * A short description of the declaration source of the Con
   */
  def desc: String
  /**
   * If the Con is a type alias, this should expand to the appropriate
   * type, given the argument list. Other types should just re-apply
   * themselves, and can use the default definition.
   */
  def expandAlias(l: Loc, self: Type, args: List[Type])(implicit su: Supply): AliasExpanded = Unexpanded(self(args:_*))
  def isInstance(p: Any): Boolean = foreignLookup.isInstance(p)
  def isTrivialConstraint: Boolean = false
  def rowConstraints: List[Type] = Nil
  def isClassConstraint: Boolean = false
}


object ClassDecl extends ConDecl {
  def desc = "class"
  override def isClassConstraint = true
}


/**
 * We enforce by construction that all row types appearing in a type
 * are either a variable, subject to some constraints, or fully
 * concrete. This is the concrete portion of that invariant.
 */
case class ConcreteRho(loc: Loc, fields: Set[Name] = Set()) extends Type {
  override def equals(v: Any) = v match {
    case ConcreteRho(_, fs) => fields == fs
    case _                  => false
  }
  override def hashCode = fields.hashCode * 111
  def at(l: Loc) = ConcreteRho(l, fields)
  override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
}

/**
 * The type constructor of ordered pairs of size n
 */
case class ProductT(loc: Loc, n: Int) extends Type {
  override def foreignLookup: Class[_] =
    if (n == 0) implicitly[ClassTag[Unit]].runtimeClass
    else implicitly[ClassTag[AnyRef]].runtimeClass
  override def unboxedForeign = n == 0
  override def equals(v: Any) = v match {
    case ProductT(_, m) => m == n
    case _ => false
  }
  override def hashCode = 38 + n * 17;
  def at(l: Loc) = ProductT(l, n)
  override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
}

/**
 * Function space
 */
case class Arrow(loc: Loc) extends Type {
  override def foreignLookup = implicitly[ClassTag[Function1[_,_]]].runtimeClass
  override def nfWith(stk: List[Type])(implicit su: Supply) = stk match {
    case l :: r :: rest => Arrow(loc, l, r).apply(rest:_*)
    case _              => this.apply(stk:_*)
  }
  override def unboxedForeign = true
  override def equals(v: Any) = v match {
    case Arrow(_) => true
    case _        => false
  }
  override def hashCode = 94 // chosen by rolling 20d8 vs water elementals
  def at(l: Loc) = Arrow(l)
  override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
}

object Arrow {
  /**
   * This is a smart constructor that helps ensure that the types it produces
   * match certain invariants. For instance the type:
   *
   *    T -> forall a. U
   *
   * is reworked to:
   *
   *    forall a. T -> U
   */
  def apply(a: Loc, e1: Type, e2: Type): Type = (e1,e2) match {
    case (Forall(d,List(),List(),p,x), Forall(e,ks,ts,q,y)) => Forall(d orElse e, ks, ts, p ++ q, AppT(AppT(Arrow(a), x), y))
    case (Forall(d,List(),List(),p,x), y)                   => Forall(d orElse y.loc, List(), List(), p, AppT(AppT(Arrow(a), x), y))
    case (Forall(d,ks,ts,p,_), _) if p.hasRowConstraints    => sys.error(e1.report("higher rank row constraint").toString)
    case (x, Forall(d,ks,ts,q,y))                           => Forall(d, ks,ts, q, AppT(AppT(Arrow(a), x), y))
    case (x, y)                                             => AppT(AppT(Arrow(a), x), y)
  }
}

case class AppT(e1: Type, e2: Type) extends Type {
  def loc = e1.loc
  override def map(f: Kind => Kind) = AppT(e1.map(f), e2.map(f))
  override def nfWith(stk: List[Type])(implicit su: Supply) = e1.nfWith(e2.nf :: stk)
  override def foreignLookup = e1.foreignLookup
  override def unboxedForeign = e1.unboxedForeign
  override def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type]) = AppT(e1.subst(ks, ts), e2.subst(ks, ts))
  var memoizedKindSchema: Option[KindSchema] = None
  override def mono = e1.mono && e2.mono
  def at(l: Loc) = AppT(e1 at l, e2)
  override def barendregtAlpha(implicit supply: Supply) = AppT(e1.barendregtAlpha, e2.barendregtAlpha)
  override def isClassConstraint = e1.isClassConstraint
  override def forget = AppT(e1.forget, e2.forget)
}
case class VarT(v: TypeVar) extends Type with Variable[Kind] {
  override def map(f: Kind => Kind) = VarT(v.map(f))
  override def toString = v.toString
  override def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type]): Type =
    ts.lift(v).getOrElse(VarT(v map (subKind(ks,_))))
  def at(l: Loc) = VarT(v at l)
}

/**
 * Exists is one of the constraint types, and exists to deal with
 * variables that occur only in constraints. Such variables should
 * _always_ be existentially quantified.
 */
class Exists(val loc: Loc, val xs: List[TypeVar] = List(), val constraints: List[Type] = List()) extends Type {
  override def map(f: Kind => Kind) = new Exists(loc, xs.map(_.map(f)), constraints.map { _ map f })
  override def toString = "Exists(%s, [%s],[%s])".format(loc, xs.mkString(", "), constraints.mkString(", "))
  override def nfWith(stk: List[Type])(implicit su: Supply) = Exists.mk(loc,xs,constraints.map(_.nf)).apply(stk:_*)
  override def subst(km: PartialFunction[KindVar,Kind], tm: PartialFunction[TypeVar,Type]) =
    Exists(loc, xs.map {_ map {_ subst km}}, constraints.map(_.subst(km,tm)))
  override def mono = false
  override def isTrivialConstraint = constraints.forall(_.isTrivialConstraint)
  override def rowConstraints = constraints.flatMap(_.rowConstraints)
  def at(l: Loc) = Exists(l, xs, constraints)
  override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
  override def barendregtAlpha(implicit supply: Supply) = {
    val nxs = xs map (v => v copy (id = supply.fresh))
    val xm  = xs.zip(nxs.map(VarT(_))).toMap
    Exists(loc, nxs, constraints.map(_.barendregtAlpha.subst(Map(), xm)))
  }
}

object Exists {
  def unit = Exists(Loc.builtin, List(), List())

  /**
   * A helper function for treating Exists and other constraints
   * uniformly when trying to peel off the former and get its
   * contents.
   */
  def unfurl(t: Type): (Loc, List[TypeVar], List[Type]) = t match {
    case Exists(l, xs, cs) => (l, xs, cs)
    case t                 => (t.loc, List(), List(t))
  }

  /**
   * A smart constructor. Maintains the invariant that we don't have
   * Exists-of-Exists, flattening down to a single exists quantifying
   * all the variables.
   */
  def apply(l: Loc, xs: List[TypeVar] = List(), q: List[Type] = List()): Type =
    if (xs.isEmpty && q.length == 1) q.head
    else {
      val (lp, ys, p) = q.foldLeft((l, xs, List[Type]())) {
        case ((lp, zs, r), Exists(l, xs, cs)) => (lp orElse l, zs ++ xs, r ++ cs)
        case ((lp, zs, r), t) => (lp orElse t.loc, zs, t :: r)
      }
      new Exists(lp, ys, p.toSet.toList)
    }

  def unapply(f : Exists): Option[(Loc, List[TypeVar], List[Type])] =
    Some((f.loc, f.xs, f.constraints))

  /**
    * a smarter smart constructor, which reorders the type arguments properly
    */
  def mk(l: Loc, xs: List[TypeVar], q:List[Type]) = {
    val xm = xs.toSet
    val nxs = typeVars(q).filter(xm(_)).toList
    Exists(l,nxs,q)
  }
}

/**
 * Universal quantification.
 *
 * We have both kind and type polymorphism, so Forall has list of both sorts of
 * variables. Every Forall also contains constraints that apply to the body,
 * which ensures that constraints do not occur at arbitrary places within
 * types (unless that is done via an otherwise empty Forall).
 */
class Forall(val loc: Loc, val ks: List[KindVar], val ts: List[TypeVar], val constraints: Type, val body: Type) extends Type {
  override def map(f: Kind => Kind) = new Forall(loc, ks, ts.map(_.map(f)), constraints.map(f), body.map(f))
  override def toString = "Forall(%s,[%s],[%s],%s,%s)".format(loc, ks.mkString(", "), ts.mkString(", "), constraints.toString, body.toString)
  override def nfWith(stk: List[Type])(implicit supply: Supply) =
    Forall.mk(loc,ks,ts,constraints.nf(supply),body.nf(supply)).apply(stk:_*)
  override def foreignLookup = body.foreignLookup
  override def unboxedForeign = body.unboxedForeign
  override def subst(km: PartialFunction[KindVar,Kind], tm: PartialFunction[TypeVar,Type]) =
    Forall(loc, ks, ts.map{_ map {_ subst km}}, constraints.subst(km,tm), body.subst(km,tm))
  override def mono = false
  def at(l: Loc) = Forall(l,ks,ts,constraints,body)
  // override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
  override def barendregtAlpha(implicit supply: Supply) = {
    val ncs = constraints.barendregtAlpha(supply)
    val nb  = body.barendregtAlpha(supply)
    val nks = ks.map(v => v copy (id = supply.fresh))
    val km  = ks.zip(nks.map(VarK(_))).toMap
    val nts = ts.map(v => subKind(km, v copy (id = supply.fresh)))
    val tm  = ts.zip(nts.map(VarT(_))).toMap
    Forall(loc, nks, nts, ncs.subst(km, tm), nb.subst(km, tm))
  }
  override def forget = Forall(loc, ks, ts, constraints.forget, body.forget)
}

object Forall {
  /**
   * A smart constructor that maintains the invariant that there are no foralls of
   * foralls. This is important for HMF checking.
   */
  def apply(l: Loc, ks: List[KindVar], ts: List[TypeVar], q: Type, b: Type): Type =
    if (ks.isEmpty && ts.isEmpty && q.isTrivialConstraint) b
    else b match {
      case Forall(lp, ksp, tsp, p, bp) => Forall(l orElse lp, ks ++ ksp, ts ++ tsp, q ++ p, bp)
      case _ => new Forall(l, ks, ts, q, b)
    }
  def unapply(f : Forall): Option[(Loc, List[KindVar], List[TypeVar], Type, Type)] =
    Some((f.loc, f.ks, f.ts, f.constraints, f.body))

  /**
   * A smarter smart constructor, which reorders the type arguments properly
   */
  def mk(l: Loc, ks: List[KindVar], ts: List[TypeVar], q: Type, b: Type): Type = b match {
    case Forall(bl, bks, bts, bq, bb) => mk(l orElse bl, ks ++ bks, ts ++ bts, q ++ bq, bb)
    case _ =>
      val km = ks.toSet
      val tm = ts.toSet
      val ats = typeVars(b)
      val nts = ats.filter(tm(_)).toList
      val nks = (kindVars(nts) ++ kindVars(b)).filter(km(_)).toList
      Forall(l,nks,nts,q,b)
  }
}

/**
 * This class represents a partition of the left side into several
 * right hand sides. We maintain no invariant that the left hand must
 * be a variable or whatnot; that is handled upon translation into a
 * format that the constraint solver can handle.
 */
class Part(val loc: Loc, val lhs: Type, val rhs: List[Type]) extends Type {
  override def map(f: Kind => Kind) = Part(loc, lhs.map(f), rhs.map(_ map f))
  override def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type]) = Part(loc, lhs.subst(ks, ts), rhs.map(_.subst(ks,ts)))
  def at(l: Loc) = Part(l, lhs, rhs)
  override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
  override def equals(v: Any) = v match {
    case Part(_, lhp, rhp) => lhs == lhp && rhs == rhp
    case _ => false
  }
  override def isTrivialConstraint = false
  override def rowConstraints = List(this)
  override def hashCode = 3 + 23 * lhs.hashCode + 5 * rhs.hashCode
  override def toString = "Part(" + lhs.toString + ", " + rhs.toString + ")"
  override def barendregtAlpha(implicit supply: Supply) = Part(loc, lhs.barendregtAlpha(supply), rhs.map(_.barendregtAlpha(supply)))

  override def forget = new Part(loc, lhs.forget, rhs.map(_.forget))
}

object Part {
  /**
   * A smart constructor that does some obvious simplifications
   * without having to get into full constraint solving.
   */
  def apply(l: Loc, lh: Type, rh: List[Type]) = {
    val (ts, rcl, ss) = rh.foldLeft((List[Type](), l, List[Name]())) {
      case ((ts,l,ss), ConcreteRho(lp, s)) => (ts, lp orElse l, s.toList ++ ss)
      case ((ts,l,ss), other) => (other ::ts, l, ss)
    }
    lh match {
      case ConcreteRho(lclhs, cs) if ts.isEmpty && ss == cs => Exists(l) // (|Foo, Bar|) <- (|Foo,Bar|)
      case ConcreteRho(lclhs, cs) if ts.length == 1 && ss.isEmpty =>
        new Part(l, ts(0), List(lh)) // flop the concrete rho to the right
      case _ if ts.isEmpty && ss.isEmpty => new Part(l,lh,Nil)           // a <- ()
      case _ if ss.isEmpty => new Part(l,lh, ts)                         // a <- b,c
      case _ if ss.toSet.size == ss.length =>                            // a <- ( (|Foo,Bar,Baz|), quux)
        new Part(l,lh,ConcreteRho(rcl, ss.toSet) :: ts)
      case _ => new Part(l,lh,rh) // otherwise: leave it alone, its complicated
    }
  }
  def unapply(p: Part) = Some((p.loc, p.lhs, p.rhs))
}

case class Memory(id: Int, body: Type) extends Type {
  def loc = body.loc
  override def map(f: Kind => Kind): Type = Memory(id, body map f)
  override def nfWith(stk: List[Type])(implicit su: Supply): Type = Memory(id, body.nf).apply(stk:_*)
  override def foreignLookup: Class[_] = body.foreignLookup
  override def unboxedForeign: Boolean = body.unboxedForeign
  override def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type]): Type =
    Memory(id, body subst (ks, ts))
  override def mono: Boolean = body mono
  override def isTrivialConstraint: Boolean = body isTrivialConstraint
  override def rowConstraints: List[Type] = body rowConstraints
  override def isClassConstraint: Boolean = body isClassConstraint
  override def at(l: Loc): Type = Memory(id, body at l)
  override def barendregtAlpha(implicit supply: Supply): Type = Memory(id, body barendregtAlpha)
  override def forget = body
}

case class TypeConDecl(
  override val foreignLookup: Class[_],
  override val unboxedForeign: Boolean
) extends ConDecl {
  def desc = "data"
}

case class FieldConDecl(fieldType: Type) extends ConDecl {
  def desc = "field"
}

class TypeAliasDecl(kindArgNames: List[KindVar], typeArgNames: List[TypeVar], body: => Type) extends ConDecl {
  override def foreignLookup: Class[_] = sys.error("foreign lookup not allowed on a type alias")
  override def unboxedForeign: Boolean = false
  def desc: String = "type"
  override def expandAlias(l: Loc, self: Type, args: List[Type])(implicit supply: Supply): AliasExpanded =
    if (args.length < typeArgNames.length)
      Bad(l.report(ordinal(typeArgNames.length,"argument", "arguments") :+: "expected, but" :+: args.length.toString :+: text("received")))
    else {
      val (xs, ys) = args.splitAt(typeArgNames.length)
      Type.expandAlias(l, subType(preserveLoc(typeArgNames.zip(xs).toMap), body).barendregtAlpha, ys)
    }

  override def isInstance(p: Any): Boolean = sys.error("isInstance not allowed on a type alias")
  override def isTrivialConstraint = body.isTrivialConstraint
  override def rowConstraints = {
    println("Warning: using rowConstraints on a typeAlias. This is probably wrong!")
    body.rowConstraints
  }
  override def isClassConstraint = {
    println("Warning: using classConstraints on a typeAlias. This is probably wrong!")
    body.isClassConstraint
  }
}

object Type {
  trait AliasExpanded {
    def map(f: Type => Type): AliasExpanded
  }
  case class Expanded(t: Type) extends AliasExpanded {
    def map(f: Type => Type) = Expanded(f(t))
  }
  case class Unexpanded(t: Type) extends AliasExpanded {
    def map(f: Type => Type) = Unexpanded(f(t))
  }
  case class Bad(d: Document) extends AliasExpanded {
    def map(f: Type => Type) = Bad(d)
  }

  /**
   * Represents most of the constructors at the type level (aside from
   * arrow and the relational types). Technically, this also includes
   * type functions that compute; aliases.
   */
  // this has to live in Type._ because otherwise the old DOS-style file handling provided by windows doesn't like CON.class
  case class Con(loc: Loc, name: Global, decl: ConDecl, schema: KindSchema) extends Type {
    def at(l: Loc) = Con(l, name, decl, schema)
    override def nfWith(stk: List[Type])(implicit su: Supply) = decl.expandAlias(loc, this, stk) match {
      case Bad(_) => this.apply(stk:_*)
      case Expanded(t) => t.nf
      case Unexpanded(t) => t
    }
    override def map(f: Kind => Kind) = Con(loc, name, decl, schema map f)
    override def foreignLookup: Class[_] = decl.foreignLookup
    override def unboxedForeign = decl.unboxedForeign
    override def subst(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type]) = Con(loc, name, decl, schema.subst(ks))
    override def equals(v: Any) = v match {
      case Con(_, oname, _, _) => name == oname
      case _ => false
    }
    override def hashCode = 92 + 13 * name.hashCode
    override def toString = name.toString + "@" + loc.toString // loc.report(name.toString).toString
    override def closeWith(vs: List[TypeVar])(implicit su: Supply) = this
    override def isTrivialConstraint = decl.isTrivialConstraint
    override def rowConstraints   = decl.rowConstraints
    override def isClassConstraint = decl.isClassConstraint
  }

  def mkConEx[C:ClassTag](s: Global, ks: KindSchema, unboxed: Boolean = true): Con =
    Con(Loc.builtin,s,TypeConDecl(implicitly[ClassTag[C]].runtimeClass, unboxed), ks)

  def mkCon[C:ClassTag](s: Global, k: Kind = star, unboxed: Boolean = true): Con =
    Con(Loc.builtin,s,TypeConDecl(implicitly[ClassTag[C]].runtimeClass, unboxed), k.schema)

  def mkRuntimeCon(s: Global, k: Kind = star, unboxed: Boolean = true): Con =
    Con(Loc.builtin,s,TypeConDecl(implicitly[ClassTag[Object]].runtimeClass, unboxed), k.schema)
  // todo: make this a foreign?

  def mkClassCon(s: Global, k: KindSchema = (star ->: constraint).schema): Con =
    Con(Loc.builtin,s, ClassDecl, k)

  // forward references into the prelude
  val bool      = mkCon[Boolean](Global("Builtin","Bool"), star, true) // constructors True and False
  val True      = Data(Global("Builtin","True"))
  val False     = Data(Global("Builtin","False"))
  val int       = mkCon[Int](Global("Builtin","Int"))
  val long      = mkCon[Long](Global("Builtin","Long"))
  val string    = mkCon[String](Global("Builtin","String"))
  val char      = mkCon[Char](Global("Builtin","Char"))
  val float     = mkCon[Float](Global("Builtin","Float"))
  val double    = mkCon[Double](Global("Builtin","Double"))
  val byte      = mkCon[Byte](Global("Builtin","Byte"))
  val date      = mkCon[Date](Global("Builtin","Date"))
  val short     = mkCon[Short](Global("Builtin","Short"))
  val field     = mkRuntimeCon(Global("Builtin","Field",Idfix), rho ->: star ->: star, false)
  val nullable  = mkRuntimeCon(Global("Builtin","Nullable",Idfix), star ->: star, false)
  val ffi       = mkCon[FFI[_]](Global("Builtin","FFI",Idfix), star ->: star, true)
  val io        = mkRuntimeCon(Global("Builtin", "IO"), star ->: star, false)
  val recordT    = mkCon[AnyRef](Global("Builtin", "Record"), rho ->: star)
  val relationT = mkCon[AnyRef](Global("Builtin", "Relation"), rho ->: star)

  implicit def relocatableType: Relocatable[Type] = new Relocatable[Type] {
    def setLoc(k: Type, l: Loc) = k at l
  }
  implicit def equalType: Equal[Type] = new Equal[Type] {
    def equal(t1:Type,t2:Type): Boolean = (t1,t2) match {
      case (Con(_,n,_,_), Con(_,m,_,_))               => n == m
      case (ConcreteRho(_,n), ConcreteRho(_,m))       => n == m
      case (ProductT(_,n), ProductT(_,m))             => n == m
      case (Arrow(_), Arrow(_))                       => true
      case (AppT(t11,t12), AppT(t21,t22))             => equal(t11,t21) && equal(t12,t22)
      case (VarT(v), VarT(w))                         => v == w
      case (Forall(_,kn,tn,q,t), Forall(_,km,tm,p,s)) => (kn == km) && (tn == tm) && (q === p) && equal(t,s)
      case (Part(_,v,c), Part(_,u,d))                 => equal(v,u) && (c === d)
      case _                                          => false
    }
  }

  implicit def TypeShow: Show[Type] = showA[Type]

  def expandAlias(l: Loc, e: Type, args: List[Type] = List())(implicit su: Supply): AliasExpanded = e match {
    case AppT(a,b)    => expandAlias(l, a, b :: args)
    case Con(_,c,d,k) => d.expandAlias(l, e,args)
    case Memory(i, b) => expandAlias(l, b, args) map (Memory(i, _))
    case _            => Unexpanded(e(args:_*))
  }

  def zipTypes[A](xs: Iterable[A], ks: Iterable[TypeVar]): Map[A,Type] = xs.zip(ks.map(VarT(_):Type)).toMap

  // import HasKindVars._

  implicit def typeHasKindVars: HasKindVars[Type] = new HasKindVars[Type] {
    def vars(t: Type): KindVars = t match {
      case Arrow(_)                => Vars()
      case AppT(e1, e2)            => vars(e1) ++ vars(e2)
      case Con(_, _, _, k)         => kindVars(k)
      case VarT(v)                 => v.extract.vars
      case Forall(_, vs, ts, q, b) => (kindVars(ts) ++ vars(b)) -- vs // deliberately excludes q
      case Exists(_, xs, q)        => kindVars(xs) ++ kindVars(q)
      case Part(_,v,c)             => vars(v) ++ kindVars(c)
      case Memory(_, body)         => vars(body)
      case _                       => Vars()
    }
    def sub(m: PartialFunction[KindVar,Kind], t: Type): Type = t.map(_.subst(m))
  }

  def typeVars[A](a: A)(implicit A:HasTypeVars[A]): Vars[Kind] = A.vars(a)
  def allTypeVars[A](a: A)(implicit A:HasTypeVars[A]): TypeVars = A.allVars(a)
  def ftvs[A](a: A)(implicit A:HasTypeVars[A]):  Traversable[TypeVar] = A.vars(a).filter(_.ty == Free)
  def fskvs[A](a: A)(implicit A:HasTypeVars[A]): Traversable[TypeVar] = A.vars(a).filter(_.ty == Skolem)

  // die, Liskov! die!
  def subType[A](ts: PartialFunction[TypeVar,Type], a: A)(implicit A:HasTypeVars[A]): A = ts match {
    case m : Map[TypeVar,Type] if m.isEmpty => a
    case _ => A.sub(Map(), ts, a)
  }

  def sub[A](ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], a: A)(implicit A:HasTypeVars[A]): A = (ks,ts) match {
    case (km : Map[KindVar,Kind], tm: Map[TypeVar,Type]) if km.isEmpty && tm.isEmpty => a
    case _ => A.sub(ks, ts, a)
  }

  def conMap(mod: String, cvs: Map[Name, TypeVar], cons: Map[Global, Con]): Map[TypeVar,Type] =
    cvs.collect {
      case (n : Global, vn) if cons.contains(n) =>
        val c = cons(n)
        (vn, c) //  at vn.loc)
      case (n : Local, vn) if cons.contains(n.global(mod)) =>
        val c = cons(n.global(mod))
        (vn, c at vn.loc)
    }

/*
  def replaceCons[A](cvs: Map[Name, TypeVar], cons: Map[Global, Con], a: A)(implicit A: HasTypeVars[A]): A = {
    val map : Map[TypeVar, Type] = cons.collect {
      case (n, c) if cvs.contains(n) =>
        val vn = cvs(n)
        (vn, c at vn.loc)
    }
    A.sub(Map(), map, a)
  }
*/

  // dangerous, may result in unannotated variables
  def dequantify(e: Type): (List[KindVar], List[TypeVar], Type, Type) = e match {
    case Forall(_, ks, ts, q, t) => (ks, ts, q, t)
    case t => (List(), List(), Exists.unit, t)
  }

  implicit def typeHasTypeVars: HasTypeVars[Type] = new HasTypeVars[Type] {
    def vars(t: Type): TypeVars = t match {
      case AppT(e1, e2)        => vars(e1) ++ vars(e2)
      case VarT(v)             => Vars(v)
      case Forall(_,ks,ts,_,b) => vars(b) -- ts
      case Exists(_,xs,qs)     => typeVars(qs) -- xs
      case Part(_, t, ts)      => vars(t) ++ typeVars(ts)
      case Memory(_, body)     => vars(body)
      case _                   => Vars()
    }
    def allVars(t: Type): TypeVars = t match {
      case AppT(e1, e2)         => allVars(e1) ++ allVars(e2)
      case VarT(v)              => Vars(v)
      case Forall(_,ks,ts,cs,b) => allVars(b) ++ allVars(cs) -- ts
      case Exists(_,xs,qs)      => typeVars(qs) -- xs
      case Part(_, t, ts)       => allVars(t) ++ allTypeVars(ts)
      case Memory(_, body)      => vars(body)
      case _                    => Vars()
    }
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], t: Type): Type = t.subst(ks,ts)
  }

  def occursCheckType(v: V[_], e: Type): Boolean = e match {
    case VarT(_)       => false
    case _             => typeVars(e).contains(v)
  }

  object Nullable {
    def unapply(ty: Type) = ty match {
      case AppT(con, t) if con == nullable => Some(t)
      case _                               => None
    }
  }

  val primNumTypes : Map[Type,PrimT] = Map(
    int    -> PrimT.IntT(),
    long   -> PrimT.LongT(),
//    float  -> PrimT.FloatT(),
    double -> PrimT.DoubleT(),
    byte   -> PrimT.ByteT(),
    short  -> PrimT.ShortT()
  )

  val primTypes : Map[Type,PrimT] = primNumTypes ++ Map(
    string -> PrimT.StringT(0),
    date   -> PrimT.DateT(),
    bool   -> PrimT.BooleanT()
//    char   -> PrimT.CharT(),
  )
}

import Type._

abstract class HasTypeVars[A] {
  def vars(a: A): TypeVars
  /** Should include even ambiguous variables */
  def allVars(a: A): TypeVars
  def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], a: A): A
}

object HasTypeVars {
  implicit def mapHasTypeVars[K,A](implicit A:HasTypeVars[A]): HasTypeVars[Map[K,A]] = new HasTypeVars[Map[K,A]] {
    def vars(xs: Map[K, A]) = xs.foldRight(Vars():TypeVars)((x,ys) => A.vars(x._2) ++ ys)
    def allVars(xs: Map[K, A]) = xs.foldRight(Vars():TypeVars)((x,ys) => A.allVars(x._2) ++ ys)
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar,Type], xs: Map[K, A]): Map[K, A] = xs.map(p => (p._1, A.sub(ks, ts, p._2)))
  }

  implicit def listHasTypeVars[A](implicit A:HasTypeVars[A]): HasTypeVars[List[A]] = new HasTypeVars[List[A]] {
    def vars(xs: List[A]) = xs.foldRight(Vars():TypeVars)((x,ys) => A.vars(x) ++ ys)
    def allVars(xs: List[A]) = xs.foldRight(Vars():TypeVars)((x,ys) => A.allVars(x) ++ ys)
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], xs: List[A]): List[A] = xs.map(A.sub(ks, ts, _))
  }

  implicit def vHasTypeVars[K,A](implicit A:HasTypeVars[A]): HasTypeVars[V[A]] = new HasTypeVars[V[A]] {
    def vars(v: V[A]) = A.vars(v.extract)
    def allVars(v: V[A]) = A.allVars(v.extract)
    def sub(ks: PartialFunction[KindVar,Kind], ts: PartialFunction[TypeVar, Type], xs: V[A]): V[A] = xs.map(A.sub(ks, ts, _))
  }
}
