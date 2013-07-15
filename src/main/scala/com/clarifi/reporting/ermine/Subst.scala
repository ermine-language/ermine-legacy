package com.clarifi.reporting
package ermine

import Document._

import com.clarifi.reporting.ermine.Relocatable.preserveLoc
import com.clarifi.reporting.ermine.Term.{ termHasTermVars, subTerm, subTermEx, zipTerms, termVars }
import com.clarifi.reporting.ermine.Type.{
  expandAlias, Bad, Expanded, Unexpanded, subType, occursCheckType, zipTypes, typeVars, Con, ftvs, fskvs,
  dequantify, primTypes, Nullable, field, int, byte, short, long, string, char, float, double, date,
  recordT
}
import com.clarifi.reporting.ermine.Kind.{ subKind, occursCheckKind, zipKinds, productKind, kindVars }
import com.clarifi.reporting.ermine.ImplicitBinding.{ implicitBindingComponents }
import com.clarifi.reporting.ermine.syntax.{
  TypeDef, DataStatement, TypeStatement, FieldStatement, ForeignDataStatement, ClassBlock, SigStatement,
  ForeignFunctionStatement, ForeignMethodStatement, ForeignValueStatement, ForeignConstructorStatement, ForeignSubtypeStatement, TableStatement, Module
}
import com.clarifi.reporting.ermine.syntax.TypeDef.typeDefComponents
import com.clarifi.reporting.ermine.parsing.{ ParseState }
import com.clarifi.reporting.ermine.Pretty.{ prettyKind, prettyType }
import scala.collection.immutable.List
import scala.collection.mutable.ListBuffer
import scalaz._
import scalaz.Free._
import scalaz.Trampoline._
import scalaz.Scalaz._
import Constraints.{ Partition, RHSConcr, RHS }
import Constraints.Q.{ PQueue }

/**
 * This module contains most of the type inference and checking machinery.
 *
 * The inference algorithm is a moderately extended version of Daan Liejen's
 * HMF, which itself extends Hindley-Milner inference with support for higher
 * rank polymorphism. By default, ordinary Hindley-Milner types will be
 * inferred, and explicit type annotations may be used to access the first-class
 * polymorphism.
 *
 * Information on HMF is available on Liejen's publicaitons page:
 *   http://research.microsoft.com/en-us/people/daan/pubs.aspx
 * specifically:
 *   http://research.microsoft.com/apps/pubs/default.aspx?id=132621
 *
 * The extensions beyond HMF are for the row types needed to include relational
 * database access within the language. This is handled by collecting constraints
 * on the types during inference, and solving them at the end. Constrained types
 * take the form 'C => t', and row constraints may only occur at the outermost
 * top-level of a type, after initial quantifiers (this invariant is maintained
 * during the inference process).
 *
 * Complications arise in that there is no unique way to write the constraints
 * for many types with regard to number and ordering of variables. For instance:
 *
 *   forall x y z. (z <- (x,y)) => [..x] -> [..y] -> [..z]
 *   forall x y z. (z <- (y,x)) => [..x] -> [..y] -> [..z]
 *   forall v w x y z. (z <- (v,w,y), x <- (v,w)) => [..x] -> [..y] -> [..z]
 *   forall w v x y z. (z <- (w,v,y), x <- (w,v)) => [..x] -> [..y] -> [..z]
 *
 * are all equivalent. The ordering of the variables in the constraint is irrelevant,
 * and we can add partitionings that don't matter and still get a valid type.
 * However, HMF relies on there being a canonical number and ordering of the variables
 * in a quantifier in order to decide if two such types unify. HMF would not detect
 * that the last two types are the same, or that the first two are compatible with
 * the latter two.
 *
 * To rectify this, we note that variables v and w appear nowhere outside the
 * constraints, and that for x, y and z, the rest of the type gives a canonical
 * ordering. Viewing the constraint arrow as implication, we can make use of the
 * fact that:
 *
 *    forall a. (P => Q) = (exists a. P) => Q
 *
 * as long as a is not free in Q, to eliminate the constraint-only variables from the
 * types that HMF must consider. Thus, we consider the latter two types ill-formed,
 * and instead insist that they be written:
 *
 *   forall x y z. (exists v w. (z <- (v,w,y), x <- (v,w))) => [..x] -> [..y] -> [..z]
 *
 * This pushes the difficulty into the constraint solver, and allows HMF to just
 * work for the remaining portion of our types.
 */

trait Requirements {
  // @throws Death on conflict, returns None when there is no such instance
  def reqs(l: Located, p: List[Type]): Option[List[Type]]
  def supers(p: List[Type]): List[Type]
}

/**`
 * The SubstState needs to keep track of the instantiations of type and kind
 * variables over the course of type inference. We maintain the invariant that
 * all the types/kinds in the map are always fully substituted, so we never
 * need to further substitute something that we look up in one of the maps.
 */
class SubstEnv(
  val classes: Map[Global,Requirements] = Map(),
  val defaults: List[Type] = List(int)
) {
  var kinds:      Map[KindVar, Kind] = Map()
  var types:      Map[TypeVar, Type] = Map()
  var remembered: Map[Int, (Subst.Gamma, Type, Loc)] = Map()
  def fskvs:      Traversable[TypeVar] = Type.fskvs(types)
  def kindVars:   Traversable[KindVar] = Kind.kindVars(kinds) ++ Kind.kindVars(types)
}

/**
 * Subst is the monad we use to do type inference/checking and unification.
 * It is a basic state+error monad, which allows us to keep track of the
 * variable instantiations we've made for unification, and throw exceptions if
 * we have a type error. Throwing an error will effectively abort the state
 * changes, rolling back the instantiations.
 *
 * Subst also supports actions for creating fresh variables, and when fed with
 * an appropriate supply, is part of maintaining the invariant that each distinct
 * variable should have a globally unique id.
 */

case class Death(error: Document, base: Exception = null) extends Exception(error.toString, base)

object Subst {
  implicit def substAlias(e: Type)(implicit su: Supply): Type =
    expandAlias(e.loc, e) match {
      case Bad(d) => die(d)
      case Expanded(t) => t
      case Unexpanded(t) => t
    }

  // OMGWTFBBQ. There is no Monoid instance for List[A]?!
  private def rep[A](n: Int)(m: => A): List[A] = {
    val list = new ListBuffer[A]()
    for (i <- 1 to n) list += m
    list.toList
  }

  def lookupType(v: TypeVar)(implicit hm: SubstEnv): Option[Type] = hm.types.get(v)
  def lookupKind(v: KindVar)(implicit hm: SubstEnv): Option[Kind] = hm.kinds.get(v)

  def substKind(e: Kind)(implicit hm: SubstEnv) : Kind = e.subst(hm.kinds)
  def substType(e: Type)(implicit hm: SubstEnv) : Type = e.subst(hm.kinds, hm.types)

/*
  def nf(t: Type)(implicit su: Supply): Type = t.nf(su)
  ...
  def close(t: Type): Type = Subst((st, su, _) => Success(t.close(su), st))
  def close(t: Term): Subst[Term] = Subst((st, su, _) => Success(t.close(su), st))
  def close(b: ImplicitBinding): Subst[ImplicitBinding] = Subst((st, su, _) => Success(b.close(su), st))
  def close(b: ExplicitBinding): Subst[ExplicitBinding] = Subst((st, su, _) => Success(b.close(su), st))
  def close(b: Binding): Subst[Binding] = Subst((st, su, _) => Success(b.close(su), st))
*/

  /*
   * Removes the specified type variables from the instantiation map.
   * In various places, we know that a variable never escapes a certain
   * scope, and it is pointless to keep instantiations for those variables
   * around, so we throw them away to save space.
   */
  def restrictTypes(xs: TraversableOnce[TypeVar])(implicit hm: SubstEnv) = hm.types = hm.types -- xs

  /*
   * See restrictTypes
   */
  def restrictKinds(xs: TraversableOnce[KindVar])(implicit hm: SubstEnv) = hm.kinds = hm.kinds -- xs

  def occursFail(v: V[_], e: Located): Nothing =
    e.die("error: infinite type: variable " + v + " = " + e)

  /*
   * This is the primitive operation underlying the unification implementation.
   * It is important to note that a variable should never be instantiated twice,
   * instantiated to itself, or instantiated to an under-substituted kind/type.
   * This function does, however, keep the types in the map fully substituted
   * in light of the new instantiation.
   */

  def instantiateKind(v: KindVar, e: Kind)(implicit hm: SubstEnv) = hm.kinds.get(v) match {
    case Some(t) => e.die("error: reinstantiated kind: " + v + " to " + e + " but it was already bound to " + t)
    case None =>
      val s = Map(v -> e)
      hm.kinds = subKind(s, hm.kinds) + (v -> e)
      hm.types = subKind(s, hm.types)
  }

  /*
   * See instantiateKind
   */
  def instantiateType(v: TypeVar, e: Type)(implicit hm: SubstEnv): Unit = hm.types.get(v) match {
    // case Some(t) if e == t => warn(e.report("warning: reinstantiated type " + v + " to the same type " + e))
    case Some(t)           => e.die("panic: reinstantiated type " + v + " to " + e + " but it was already bound to " + t)
    case None              =>
      hm.types = subType(Map(v -> e), hm.types) + (v -> e)
      hm.remembered = hm.remembered.map { case (k, (g, t, loc)) => (k, (subType(Map(v -> e), g), subType(Map(v -> e), t), loc)) }
  }

  /**
   * This is a higher level interface to the unification machinery than the above
   * instantiate functions. It will appropriately handle unifying a variable with
   * itself, but unifying under-substituted kinds/types _will_ lead to improper
   * instantiations, so it is important to keep values fully substituted during
   * checking.
   *
   * The function returns a fully-substituted version of the unified kind with
   * extra location information.
   */
  def unifyKind(e1: Kind, e2: Kind)(implicit hm: SubstEnv, tyl: Located): Kind = (e1,e2) match {
    case (VarK(u), VarK(v)) if u.id == v.id => e1
    case (VarK(v), e) if v.ty != Skolem =>
      if (occursCheckKind(v, e)) occursFail(v, e)
      else { instantiateKind(v, e); e }
    case (e, VarK(v)) if v.ty != Skolem =>
      if (occursCheckKind(v, e)) occursFail(v, e)
      else { instantiateKind(v, e); e }
    case (ArrowK(l1,c1, t1), ArrowK(l2, c2, t2)) =>
      val c3  = unifyKind(c1, c2)
      ArrowK(l1 unifiedWith l2, c3, unifyKind(substKind(t1), substKind(t2)))
    case _ if (e1 == e2) => e1
    case _ => tyl.die("error: failed to unify kind" :+: prettyKind(e1) :+: "with kind" :+: prettyKind(e2))
  }

  /**
   * See unifyKind
   */
  // probably needs to unify more kinds than we currently do
  def unifyType(e1z: Type, e2z: Type)(implicit hm: SubstEnv, su: Supply, tml: Located): Type = {
    val e1 = substAlias(e1z)
    val e2 = substAlias(e2z)
    (e1, e2) match {
      case (Memory(i, b), t) =>
        val tp = unifyType(b, t)
        val oldr = hm.remembered
        hm.remembered = oldr + (i -> (oldr(i)._1, tp, b.loc))
        tp
      case (t, Memory(i, b)) =>
        val tp = unifyType(t, b)
        val oldr = hm.remembered
        hm.remembered = oldr + (i -> (oldr(i)._1, tp, b.loc))
        tp
      case (VarT(u), VarT(v)) if u.id == v.id => e1
      case (VarT(v), e) if v.ty != Skolem =>
        if (occursCheckType(v, e)) occursFail(v, e)
        else { kindCheck(List(), e, v.extract) ; instantiateType(v, e); e }
      case (e, VarT(v)) if v.ty != Skolem =>
        if (occursCheckType(v, e)) occursFail(v, e)
        else { kindCheck(List(), e, v.extract) ; instantiateType(v, e); e }
      case (AppT(c1, t1), AppT(c2, t2)) =>
        val c3 = unifyType(c1, c2)
        val t3 = unifyType(substType(t1),substType(t2))
        AppT(substType(c3), t3)
      case (Forall(ln,kns,ns,q,nf), Forall(lm,kms,ms,p,mf)) =>
        if (!q.isTrivialConstraint) tml.die("Unable to unify with constraints", e1.toString, e2.report(e2.toString))
        if (!p.isTrivialConstraint) tml.die("Unable to unify with constraints", e2.toString, e1.report(e1.toString))
        if (!(kns.length == kms.length && ns.length == ms.length)) tml.die("Unable to unify with mismatched arity", e1.toString, e2.report(e2.toString))
        val sks = kns.zip(kms).map({ case (n,m) => fresh(n.loc.instantiatedBy(ln unifiedWith lm), n.name.orElse(m.name), Skolem, ()) }).toList
        val skvs = sks.map(VarK(_)).toList
        val nkm = zipKinds(kns,sks)
        val mkm = zipKinds(kms,sks)
        val nsp = subKind(nkm, ns)
        val msp = subKind(mkm, ms)
        val sts = nsp.zip(msp).map({
          case (n,m) =>
            val o = unifyKind(n.extract,m.extract)
            fresh(o.loc.instantiatedBy(ln unifiedWith lm), n.name.orElse(m.name), Skolem, o)
        }).toList
        val ntm = zipTypes(ns,sts)
        val mtm = zipTypes(ms,sts)
        unifyType(subType(ntm, nf), subType(mtm, mf))
        bientail(q,p)

        checkSkolemEscape(sts, List(), None, false)

        Forall(ln unifiedWith lm, kns, ns, substType(q), substType(nf))
      case (p : Exists, q) => tml.die("panic: unifying existential", q.report("note: with this type"))
      case (p, q : Exists) => tml.die("panic: unifying existential", p.report("note: with this type"))
      case _ if (e1 == e2) => e1
      case _ => tml.die("error: failed to unify type" :+: prettyType(e1) :+: "with type" :+: prettyType(e2))
    }
  }

  def checkSkolemEscape(ssz: Traversable[TypeVar], mask: Traversable[TypeVar], ot: Option[Type], suppress: Boolean)(implicit hm: SubstEnv, tml: Located): Unit =
    if (!suppress) {
      val ss = ssz.toSet

      ot match {
        case None => ()
        case Some(t) =>
          val escs = fskvs(t).filter(ss(_))
          if (escs nonEmpty)
            tml.die("error: skolem variables escape:", text("Type would have been:") :/+: prettyType(t, -1))
      }

      val hescs = fskvs(hm.types -- mask).filter(ss(_))
      if (hescs nonEmpty)
        tml.die("error: skolem variables escape in environment", hescs.mkString(", "))
    }

  def unfurlApp(p: Type, args: List[Type] = List()): Option[(Con, List[Type])] = p match {
    case AppT(f,x)      => unfurlApp(f, x::args)
    case c : Con        => Some((c, args))
    case _              => None
  }

  def bySuper(p: Type)(implicit hm: SubstEnv): List[Type] = unfurlApp(p) match {
    case Some((c,args)) => hm.classes.get(c.name) match {
      case None    => c.die("Unknown class")
      case Some(d) => p :: d.supers(args).flatMap(bySuper(_))
    }
    case None => List()
  }

  def byInst(p: Type)(implicit hm: SubstEnv): Option[List[Type]] = unfurlApp(p) match {
    case Some((c,args)) => hm.classes.get(c.name) match {
      case None    => c.die("Unknown class")
      case Some(d) => d.reqs(p.loc, args)
    }
    case None => None
  }

  def entails(ps: List[Type], p: Type)(implicit hm: SubstEnv): Boolean =
    ps.flatMap(bySuper(_)).exists(p == _) || (
      byInst(p) match {
        case None => false
        case Some(qs) => qs.forall { entails(ps,_) }
      }
    )

  def simplifyPredicates(ps0: List[Type])(implicit hm: SubstEnv): List[Type] = {
    def go(rs: List[Type], pss: List[Type]): List[Type] = pss match {
      case List()  => rs
      case p :: ps => if (entails(rs ++ ps, p)) go(rs, ps)
                      else go(p :: rs, ps)
    }
    go(List(), ps0)
  }

  def pnf(p: Type): Boolean = p match {
    case v : VarT  => true
    case AppT(l,_) => pnf(l)
    case c : Con   => false
    case _         => false
  }

  def isPNF(p: Type): Boolean = unfurlApp(p) match {
    case None => false
    case Some((c,args)) => args.forall(pnf(_))
  }

  def toPNFs(ps: List[Type])(implicit hm: SubstEnv, tml: Located): List[Type] =
    ps.flatMap(toPNF(_))

  def toPNF(p: Type)(implicit hm: SubstEnv, tml: Located): List[Type] = byInst(p) match {
    case None =>
      if (isPNF(p)) List(p)
      else tml.die("No instance for " + prettyType(p))
    case Some(ps) => toPNFs(ps)
  }

  def reduce(ps: List[Type])(implicit hm: SubstEnv, tml: Located): List[Type] = {
    val (parts,cs) = ps.partition(_.isInstanceOf[Part])
    parts ++ simplifyPredicates(toPNFs(cs))
  }

  case class Ambiguity(v: TypeVar, preds: List[Type]) {
    def default(implicit hm: SubstEnv): Option[Type] = {
      def simple(p: Type) = unfurlApp(p) match {
        case Some((c,List(VarT(u)))) => u == v
        case _ => false
      }
      if (preds forall simple)
        hm.defaults.filter({ c =>
          preds.forall(p => entails(List(),subType(Map(v -> c), p)))
        }).headOption
      else None
    }
  }

  def ambiguitiesIn(vs: List[TypeVar], ps: List[Type]): List[Ambiguity] =
    vs.map(v => Ambiguity(v, ps.filter(p => typeVars(p).exists(_ == v)))).filter(a => a.preds.nonEmpty)

  def ambiguities(vs: TypeVars, ps: List[Type]): List[Ambiguity] =
    ambiguitiesIn((typeVars(ps) -- vs).toList, ps)

  def defaultSubst(l: Located, ambs: List[Ambiguity])(implicit s: SubstEnv): Map[TypeVar,Type] =
    ambs.map(a => a.default match {
      case Some(d) => a.v -> d
      case None => a.v.die(
        "Unable to resolve ambiguous constraints" :+:
        oxford("and", a.preds.map(prettyType(_)))
      )
    }).toMap

  def split(g: Gamma, gs: TypeVars, ps: List[Type])(implicit hm: SubstEnv, tml: Located): (List[Type],List[Type]) = {
    val fs = typeVars(g)
    val gvs = fs.toSet
    val (ds, rs) = reduce(ps).partition { typeVars(_).forall(gvs) }
    val ambs = ambiguities(fs ++ gs, rs)
    (ds, (rs.toSet -- ambs.flatMap(_.preds)).toList)
  }

  def entail(p: Type, q: Type)(implicit hm: SubstEnv, su: Supply) {
    val (vs, ps) = unbindExists(Free,p)
    val (us, qs) = unbindExists(Free,q)
    for (q <- qs)
      if (q.isClassConstraint && !entails(ps,q))
        q.die(
          prettyType(q) :+: text("not entailed given known constraints"),
          ps.map(p => p.report("known constraint" :+: prettyType(p))):_*
        )
  }

  def bientail(p: Type, q: Type)(implicit hm: SubstEnv, su: Supply) {
    entail(p,q)
    entail(q,p)
  }

  /**
   * The matchFun functions assert that the type/kind passed in must be a function
   * space. With free variables and quantifiers, this is not a simple case of
   * pattern matching, so these helper functions will perform the necessary work,
   * and return the quantifier information, domain and codomain of the function
   * space.
   */
  def matchFunKind(ks: KindSchema)(implicit hm: SubstEnv, su: Supply, tyl: Located): (List[KindVar],Kind,Kind) = unbindKindSchema(Free,ks) match {
    case (vs, ArrowK(l, x, y)) => (vs, x, y)
    case (vs, VarK(v)) =>
      val li = v.loc.inferred
      val x = VarK(fresh(li, none, Free, ()))
      val y = VarK(fresh(li, none, Free, ()))
      instantiateKind(v, ArrowK(li, x, y))
      (vs, x, y)
    case _ => tyl.die("Could not match kind" :+: prettyKind(ks.body) :+: "against kind (k1 -> k2)")
  }

  /**
   * See matchFunKind
   */
  def matchFunType(tz: Type)
                  (implicit hm: SubstEnv, su: Supply, tml: Located): (List[KindVar],List[TypeVar],Type,Type,Type) = {
    val t = substAlias(tz)
    def rawMatch(r: Type) = r match {
      case AppT(AppT(Arrow(_), x), y) => (List(), x, y)
      case VarT(v)  =>
        val li = v.loc.inferred
        val x = fresh(li, none, Free, Star(li))
        val y = fresh(li, none, Free, Star(li))
        instantiateType(v, Arrow(li, VarT(x), VarT(y)))
        (List(x,y), VarT(x), VarT(y))
      case _ => tml.die("Could not match type" :+: prettyType(t) :+: "against type (t1 -> t2)")
    }
    unbind(Free,t) match {
      case (ks, ts, q, Memory(i, b)) =>
        val (l, x, y) = rawMatch(b)
        val oldr = hm.remembered
        hm.remembered = oldr + (i -> (oldr(i)._1, Arrow(b.loc)(x,y), b.loc))
        (ks, ts ++ l, q, x, y)
      case (ks, ts, q, b) =>
        val (l, x, y) = rawMatch(b)
        (ks, ts ++ l, q, x, y)
    }
  }

  /**
   * Ensures that the type t has a kind compatible with k.
   * The returned kind incorporates any unifications that happened to k
   * during the process.
   */
  def kindCheck(d: Delta, t: Type, k: Kind)(implicit hm: SubstEnv, su: Supply, tyl: Located): Kind = {
    val tks = inferKind(d, t)
    val (vs, tk) = unbindKindSchema(Free, tks)
    val kp = unifyKind(substKind(k), tk)
    restrictKinds(vs)
    kp
  }

  /**
   * Infers the kind of a given type.
   *
   * The Delta parameter keeps track of what variables may be generalized in
   * the local inference context.
   */
  def inferKind(d: Delta, t: Type)(implicit hm: SubstEnv, su: Supply): KindSchema = {
    val li = t.loc.inferred
    implicit val tyl: Located = t
    t match {
      case VarT(v)          => substKind(v.extract).schema
      case Arrow(_)         => ArrowK(li,Star(li), ArrowK(li, Star(li), Star(li))).schema
      case ProductT(_,n)    => productKind(li,n).schema
      case ConcreteRho(_,_) => Rho(li).schema
      case Part(_,x,ys)     =>
        kindCheck(d, x, Rho(li))
        for (y <- ys) kindCheck(d, substType(y), Rho(li))
        Constraint(li).schema
      case a@AppT(f, x) => a.memoizedKindSchema match {
        case Some(ks) => ks
        case None =>
          val (fvs, i, o) = matchFunKind(inferKind(d, f))
          val (xvs, kx) = unbindKindSchema(Free, inferKind(d, substType(x)))
          unifyKind(substKind(i), kx)
          val op = generalizeKind(substDelta(d), substKind(o)) at li
          restrictKinds(fvs ++ xvs)
          if (op.isClosed) { a.memoizedKindSchema = Some(op); op } else op
      }
      case Exists(l,xs,ts) =>
        val nxs = refreshList(Ambiguous(Skolem), l, xs)
        for (c <- subType(zipTypes(xs,nxs), ts)) kindCheck(d, substType(c), Constraint(li))
        restrictTypes(nxs)
        Constraint(li).schema
      case Forall(l,ks,ts,q,tp) =>
        val km = zipKinds(ks, refreshList(Skolem, l, ks))
        val tm = zipTypes(ts, refreshList(Skolem, l, subKind(km, ts)))
        kindCheck(d, tp.subst(km, tm), Star(li))
        kindCheck(d, q.subst(km, tm), Constraint(li))
        Star(li).schema
      case Con(_,_,_,s) => s
    }
  }

  /**
   * Checks that e2 subsumes e1. This means that a value of type e2 may be
   * used in any place that a value of type e1 is expected.
   *
   * Due to the way HMF works, this only handles 'one level' of the induced
   * subtyping relation that quantification provides. That is:
   *
   *   (forall a. a) <~ (forall a. a -> a)                 works
   *   ((forall a. a -> a) -> T) <~ ((forall a. a) -> T)   dies
   *
   * where T <~ U means T subsumes U.
   */
  def subsumeType(e1: Type, e2: Type)(implicit hm: SubstEnv, su: Supply, tml: Located): (Type, Type) = {
    val (sks, sts, qz, r1) = unbind(Skolem, e1)
    val (tks, tts, pz, r2) = unbind(Free, e2)
    val r3 = unifyType(r1, r2)
    val q = substType(qz)
    val (qxs, qs) = unbindExists(Free, q)
    val (pxs, ps) = unbindExists(Free, substType(pz))
    val (ds, rs)  = ps.partition(p => Type.fskvs(p).isEmpty)
    for (r <- rs)
      entails(qs,r)
    restrictTypes(qxs) // ?
    restrictTypes(pxs) // ?
    restrictKinds(tks)
    restrictTypes(tts)
    val skss = sks.toSet
    val stss = sts.toSet
    val escs = hm.fskvs.filter(v => stss.contains(v)) ++ hm.kindVars.filter(skss(_))
    if (escs nonEmpty)
      tml.die(vsep(List(
        text("type t1 did not subsume t2: "),
        text("  t1 :") :+: prettyType(e2,-1),
        text("  t2 :") :+: prettyType(e1,-1),
        e2.report("t1"),
        e1.report("t2")
      )))
    // tml.die("error: escaping Skolem variables: " + escs.mkString(", "), e1.toString, e2.report(e2.toString))
    (q,Exists(pz.loc, pxs, ds))
  }

  /**
   * Peels an existential quantifier off of a type, refreshing the variables quantified
   * to the given VarType, and returning the list of new variables.
   *
   * If the type is not existentially quantified, we may consider it to be wrapped in
   * an existential quantifying zero variables (which should technically never appear,
   * due to our keeping types in a normalized form), and appropriate values are returned.
   */
  def unbindExists(ty: VarType, t: Type)(implicit su: Supply): (List[TypeVar],List[Type]) = t match {
    case Exists(l,xs,qs) =>
      val nxs = refreshList(Ambiguous(ty), l, xs)
      (nxs, subType(zipTypes(xs, nxs), qs))
    case _ => (List(), List(t))
  }

  /**
   * Peels a universal quantifier off a type, similar to unbindExists.
   *
   * The returned values are the refereshed kind and type variables, the constraints,
   * and the freshened type inside the quantifier.
   */
  def unbind(ty: VarType, t: Type)(implicit su: Supply, hm: SubstEnv): (List[KindVar], List[TypeVar], Type, Type) = substAlias(t) match {
    case Memory(i, b) =>
      val (ks, ts, q, bp) = unbind(ty, b)
      (ks, ts, q, Memory(i, bp))
    case Forall(l,ks,ts,q,b) =>
      val nks = refreshList(ty, l, ks)
      val km  = zipKinds(ks, nks)
      val nts = refreshList(ty, l, subKind(km, ts))
      val tm  = zipTypes(ts, nts)
      hm.remembered = hm.remembered map { case (k, (g, t, loc)) => (k, (Type.sub(km, tm, g), t subst (km, tm), loc)) }
      (nks,nts,q.subst(km,tm),b.subst(km,tm))
    case _ => (List(), List(), Exists(t.loc.inferred), t)
  }

  /**
   * See unbind.
   */
  def unbindKindSchema(ty: VarType, s: KindSchema)(implicit su: Supply): (List[KindVar],Kind) = {
    val nks = refreshList(ty, s.loc, s.forall)
    (nks, s.body.subst(zipKinds(s.forall,nks)))
  }

  /**
   * See unbind.
   */
  def unbindAnnot(g: Gamma, a: Annot)(implicit hm: SubstEnv, su: Supply): (List[KindVar], List[TypeVar],Type) = {
    val nks = refreshList(Free, a.loc, a.eksists)
    val km = zipKinds(a.eksists, nks)
    val nxs = refreshList(Free, a.loc, subKind(km, a.exists))
    val t = a.body.subst(km, zipTypes(a.exists, nxs))
    implicit val loc: Located = a
    kindCheck(delta(g), t, Star(a.loc.inferred))
    (nks, nxs, substType(t))
  }

  /**
   * A Delta is a context for keeping track of which kind variables may be generalized
   * over during a portion of kind checking.
   */
  type Delta = List[Kind]
  def substDelta(g: Delta)(implicit hm: SubstEnv): Delta = g.map(substKind(_)).toList
  def delta(g: Gamma): Delta = kindVars(g).map(VarK(_)).toList

  /**
   * A Gamma is a context for keeping track of which type variables may be generalized
   * over during a portion of type checking. Since types may also contain kinds, this
   * induces a Delta that may be extracted when switching from type checking to kind
   * checking.
   */
  type Gamma = List[TermVar]
  def substGamma(g: Gamma)(implicit hm: SubstEnv): Gamma = g.map(v => v.map(substType(_))).toList

  /**
   * Ensures that a term e has a type compatible with t, in context g.
   * Specifically, t must be subsumed by the inferred type of e.
   */
  def typeCheck(g: Gamma, e: Term, tz: Type)(implicit hm: SubstEnv, su: Supply) {
    val et = inferType(g, e)
    val t = substType(tz)
    implicit val tml: Located = e
    kindCheck(delta(g), t, Star(e.loc.checked))
    val (q,p) = subsumeType(substType(t), substType(et))
    // TODO: ADD warnings here later if we need to check subsumption involving constraints
    ()
  }

  /**
   * Checks that the given type for an explicit bindings is subsumed by the
   * inferred type, analogously to typeCheck.
   */
  def typeCheckExplicitBinding(g: Gamma, binding: ExplicitBinding)(implicit hm: SubstEnv, su: Supply) {
    val li = binding.loc.inferred
    implicit val tml: Located = binding
    val (kvs, tvs, ty) = unbindAnnot(g, binding.ty)
    kindCheck(delta(g), ty, Star(li))
    val typ = substType(ty)
    val args = rep(binding.arity) { VarT(fresh[Kind](li, None, Free, Star(li))) }
    val f = inferAltTypes(binding.loc, g, binding.alts, args) { r => args.foldRight(r)(Arrow(li, _, _)) }
    val (q,p) = subsumeType(typ, f)
    restrictKinds(kvs)
    restrictTypes(tvs)
    // _ <- unifyType(binding.ty, v.extract)
    ()
  }

  // we'll need thih-style split and defaulting as well, when we actually add classes

  // data Eq {k} (a : k) (b : k) = Eq (forall p. p a -> p b) -- can we eliminate these explicit kindArgs as we never monomorphize?

  // infer kinds for a mutually recursive block of type defs
  def inferTypeDefKindSchemas(bs: List[TypeDef])(implicit hm: SubstEnv, su: Supply): List[(KindSchema, TypeDef)] = {
    // make up variables for the result kinds
    val rks = bs.map(v => VarK(fresh[Unit](v.loc.inferred, None, Free, ()))).toList
    val bsp = bs.zip(rks).map { case (b,k) => b asRho k }
    val bspp = subType(bsp.map(b => b.v -> VarT(b.v)).toMap, bsp)
    // now that we all agree on variables, lets run inference
    bspp.zip(rks).foreach {
      case (b@DataStatement(l, v, kindArgs, typeArgs, cons), rk) =>
        implicit val tyl: Located = l
        unifyKind(substKind(b rho rk), substKind(v.extract))
        unifyKind(substKind(rk), Star(l.inferred))
        cons.foreach { case (es, _, ts) =>
          for (dd <- ts)
            kindCheck(typeArgs.map(t => substKind(t.extract)) ++ es.map(t => substKind(t.extract)),
              substType(dd), Star(l.inferred))
        }
      case (b@ClassBlock(l, v, kindArgs, typeArgs, ctx, privates, statements), rk) =>
        implicit val tyl: Located = l
        unifyKind(substKind(b rho rk), substKind(v.extract))
        unifyKind(substKind(rk), Constraint(l.inferred))
        statements.foreach {
          case SigStatement(lp,_,tz) => kindCheck(typeArgs.map(t => substKind(t.extract)), substType(tz), Star(lp.inferred))
          case _ => ()
        }
      case (TypeStatement(l, v, kindArgs, typeArgs, body), rk) =>
        val d = typeArgs.map(t => substKind(t.extract))
        val (kvs, k) = unbindKindSchema(Free, inferKind(d, substType(body)))
        implicit val tyl: Located = l
        unifyKind(k, substKind(rk))
        restrictKinds(kvs)
    }

    bspp.map {
      case b =>
        val gk = generalizeKind(b.typeArgs.map(_.extract), substKind(b.v.extract))
        val typeArgs = b.typeArgs.map { a => a.map(substKind(_)) }
        (gk, b match {
          case DataStatement(l, v, kindArgs, _,        cons) =>
               DataStatement(l, v, kindArgs, typeArgs, cons.map { case (es, v, ts) => (es, v, ts.map(substType(_))) })
          case ClassBlock(l, v, kindArgs, _, ctx, privates, statements) =>
               ClassBlock(l, v, kindArgs, typeArgs, ctx, privates, statements.map {
                 case SigStatement(l,vs,t) => SigStatement(l,vs,substType(t))
                 case t => t
               })
          case TypeStatement(l, v, kindArgs, _, body) =>
               TypeStatement(l, v, kindArgs, typeArgs, substType(body))
        })
    }
  }

  /**
   * Infers the types of a binding group, either top level or local.
   *
   * At this point, the series of bindings has already been split into strongly
   * connected components so as to infer the most general types possible. The
   * procedure we take for this is as follows:
   *
   *   1) (Temporarily) assume given type annotations are correct, and make sure
   *      all variables thus defined are substituted into the other bindings.
   *   2) Infer each of the un-annotated components in topological order, substituting
   *      the inferred and generalized types into subsequent components as appropriate.
   *   3) Check that the explicitly annotated bindings actually have their specified
   *      type, given the inferred types for the implicit bindings.
   *
   * The returned map is for substituting variables with versions carrying a proper
   * type, as inferred by this process.
   *
   * The returned Gamma treats the binding group's type as being in the context,
   * which is appropriate for checking the body of a let.
   */
  def inferBindingGroupTypes(l: Loc,
                             g: Gamma,
                             is: List[ImplicitBinding],
                             es: List[ExplicitBinding],
                             slv: Boolean = false)(implicit hm: SubstEnv, su: Supply): (Gamma, List[Type], Map[TermVar,TermVar]) = {
    val etm = es map {
      case e =>
        val (_, tvs, ty) = unbindAnnot(g, e.ty)
        if (tvs.nonEmpty)
          e.die("panic: Unsupported scoped type variables: " + tvs)
        e.v -> ty
    } toMap
    val em = etm map { case (v, t) => (v, v as t) }
    val esp = es.map(e => e.subst(Map(), Map(), em))
    val isp = is.map(i => i.subst(Map(), Map(), em))
    val (ds, subs) = mapAccum_((List[Type](), Map():Map[TermVar,TermVar]), implicitBindingComponents(isp)) {
       case ((ds0, subs), is) =>
          val (ds,isp) = inferImplicitBindingTypes(l, g ++ toGamma(subs), subTerm(subs,is), slv)
          (ds ++ ds0, subs ++ isp)
    }
    for (e <- esp) typeCheckExplicitBinding(g, subTerm(subs, e.copy(ty = Annot.plain(e.loc, substType(etm(e.v))))))
    val el = esp.map({ e => e.v -> e.v.as(substType(etm(e.v))) }).toList
    is.foreach {
      case ImplicitBinding(_, v, _, Some(i)) =>
        hm.remembered = hm.remembered + (i -> (g, subs(v).extract, l))
      case _ => ()
    }
    (g ++ toGamma(subs), ds, el.toMap ++ subs)
  }

  /**
   * This function infers the types of a single strongly connected component.
   * The proper procedure for this is to infer while avoiding generalizing on
   * _any_ of the types in the binding group, and then generalize all the
   * types so inferred afterward.
   *
   * The returned map is for substituting variables with versions carrying the
   * type we have inferred.
   */
  def inferImplicitBindingTypes(l: Loc,
                                omgz: Gamma,
                                bs: List[ImplicitBinding],
                                slv: Boolean)(implicit hm: SubstEnv, su: Supply): (List[Type],Map[TermVar,TermVar]) = {

    val ((g, cs), ts) = mapAccum((omgz ++ bs.map(_.v), List[Type]()), bs) {
      case ((g, cs), b) =>
        val args = rep(b.arity) { VarT(fresh[Kind](b.loc.inferred, None, Free, Star(l))) }
        val r = inferAltTypes(b.loc, g, b.alts, args) {
          tau => args.foldRight(tau) { Arrow(b.loc.inferred, _, _) }
        }
        val tp = substType(b.v.extract)
        val (tks, tts, s, rp) = unbind(Free, r)
        val (_, csp) = unbindExists(Free, s)
        implicit val tml: Located = b
        subsumeType(tp, rp)
        restrictKinds(tks)
        restrictTypes(tts)
        ((substGamma(g), csp ++ cs), substType(tp))
    }
    val omg = substGamma(omgz)
    val gvs = typeVars(omg).toSet
    val (ds, rs) = cs.partition(c => typeVars(c).forall(gvs))
//    for (r <- rs)
//      for (c <- r.rowConstraints)
//        if (typeVars(c).exists(gvs))
//          l.die("Disallowed local row constraints on ambient variables")

    implicit val tml: Located = l
    val csp = if (slv) solve(Exists(l, List(), rs))
              else Exists(l, List(), rs)
    (ds, bs.zip(ts).map({
      case (b,t) =>
        implicit val tml: Located = b
        b.v -> b.v.as(generalize(omg, csp, substType(t).forget))
    }).toMap)
  }

  def toGamma(m: Map[TermVar,TermVar]): Gamma = m.values.toList

  // NB: the inferred type has kind star
  def inferType(g: Gamma, e: Term, suppressEscapes:Boolean = false)(implicit hm: SubstEnv, su: Supply): Type = {
    val li = e.loc.inferred
    implicit val tml: Located = e
    val ty = e match {
      case Var(v)          => substType(v.extract)
      case Rigid(e)        => inferType(g, e, suppressEscapes)
      case LitInt(_, i)    => int at li
      case LitByte(_, i)   => byte at li
      case LitShort(_, i)  => short at li
      case LitLong(_, l)   => long at li
      case LitString(_, s) => string at li
      case LitChar(_,c)    => char at li
      case LitFloat(_,f)   => float at li
      case LitDouble(_,d)  => double at li
      case LitDate(_,_)    => date at li
      case EmptyRecord(_)   => (recordT at li)(ConcreteRho(li, Set()))
      case Sig(l, x, ann) =>
        val (kvs, bvs,t) = unbindAnnot(g, ann)
        typeCheck(g, x, t)
        val tp = substType(t)
        restrictKinds(kvs)
        restrictTypes(bvs)
        location[Type].mod(_.instantiatedBy(li), tp)
      case Product(_, n) =>
        val vs = rep(n)(fresh(li, none, Free, Star(li)))
        val ts = vs.map(VarT(_):Type)
        Forall(li, List(), vs, Exists(li), ts.foldRight(ProductT(li, n)(ts:_*))(Arrow(li, _, _)))
      case Case(_, e, alts) =>
        val t = inferType(g, e, suppressEscapes)
        inferAltTypes(li, g, alts, List(t), suppressEscapes)(x => x)
      case Let(l, is, es, body) =>
        val (gp,ds,m) = inferBindingGroupTypes(l, g, is, es, true)
        val (ks, ts, c, t) = unbind(Free, inferType(gp, subTerm(m, body), suppressEscapes))
        val r = generalize(substGamma(gp), Exists(c.loc,List(),c :: ds.map(substType(_))), t)
        restrictKinds(ks)
        restrictTypes(ts)
        r
      case App(f, x) =>
        val tf = inferType(g, f, suppressEscapes)
        val (ks, txs, r, i, o) = matchFunType(tf)
        val gp = substGamma(g)
        val tx = inferType(gp, x, suppressEscapes)
        val pp = if (x.isAnnotated) { unifyType(substType(i), tx); Exists(li) }
             else {
               val (q,p) = subsumeType(substType(i), tx)
               if (q.hasRowConstraints) e.die("error: higher rank row constraint in application")
               else p
             }
        val op = generalize(substGamma(gp), substType(r ++ pp), substType(o))
        restrictKinds(ks)
        restrictTypes(txs)
        op
      case Lam(l, p, f) =>
        val pt = inferPatternType(g, p)
        val sigma = pt.extract
        val vsp = refreshList(Free, li, pt.vs)
        val expr = subTerm(zipTerms(pt.vs, vsp),f)
        val tauz = inferType(vsp ++ substGamma(g), expr, suppressEscapes)
        val (ks, ts, q, tau) = if (expr.isAnnotated) (List(),List(),Exists(li), tauz)
                               else unbind(Free,tauz)
        val tanns = pt.xs.map(v => substType(VarT(v))).toList
        val ptanns = tanns.filterNot(_.mono)
        if (ptanns nonEmpty) e.die("error: unannotated parameters used polymorphically")
        val r = generalize(substGamma(g), substType(q), substType(Arrow(li)(sigma, tau)))
        restrictKinds(ks)
        restrictTypes(ts ++ pt.xs)
        // we need to check for skolem escape in case a match introduced them.
        checkSkolemEscape(pt.ss, List(), Some(r), suppressEscapes)
        r
      case Hole(_) =>
        val a = fresh(li, none, Bound, Star(li))
        Forall(li, List(), List(a), Exists(li), VarT(a))
      case Remember(i, e) =>
        val t = inferType(g, e, suppressEscapes)
        hm.remembered = hm.remembered + (i -> (g,t,e.loc))
        Memory(i, t)
    }
    trySolveOn(substGamma(g), ty)
  }

  // gives back a list of term variables bound by the pattern and a list of type variables that were quantified
  case class Patterned[+A](
    extract: A,
    vs: List[TermVar] = List(),
    xks: List[KindVar] = List(),
    ss: List[TypeVar] = List(),
    xs: List[TypeVar] = List(),
    constraints: List[Type] = List()
  ) extends Comonadic[Patterned,A] with Applied[Patterned,A] {
    def self = this
    def lift[B](p: Patterned[B]) = p
    def extend[B](f: Patterned[A] => B) = Patterned(f(this),vs,xks,ss,xs,constraints)
    def map2[B,C](m: => Patterned[B])(f: (A,B) => C): Patterned[C] = Patterned(f(extract,m.extract), vs ++ m.vs, xks ++ m.xks, ss ++ m.ss, xs ++ m.xs, constraints ++ m.constraints)
  }

  def typeCheckPattern(g: Gamma, e: Pattern, tz: Type)(implicit hm: SubstEnv, su: Supply): Patterned[Unit] = {
    val pt = inferPatternType(g, e)
    val t = substType(tz)
    implicit val tml: Located = e
    kindCheck(delta(g), t, Star(e.loc.checked))
    val (q,p) = subsumeType(substType(t), substType(pt.extract))
    pt skip
  }

  def inferPatternTypes(g: Gamma, es: List[Pattern])(implicit hm: SubstEnv, su: Supply): Patterned[List[Type]] = {
    val ps = es.map(p => inferPatternType(g,p)).toList // TODO: this needs to do type substitution into the patterns once we have scoped type variables
    Patterned(ps.map(_.extract), ps.flatMap(_.vs), ps.flatMap(_.xks), ps.flatMap(_.ss), ps.flatMap(_.xs), ps.flatMap(_.constraints))
  }

  def kindChecks(g: Gamma, ts: List[Type], kind: Kind)(implicit hm: SubstEnv, su: Supply): Gamma = ts match {
    case t :: ts =>
      implicit val loc: Located = t
      kindCheck(delta(g), t, kind)
      kindChecks(substGamma(g), ts, kind)
    case _ => g
  }

  def inferAltTypesPrime(
    l: Loc,
    g: Gamma,
    alts: List[Alt],
    ts: List[Type],
    result: Type,
    qs : List[Type] = List(),
    rkinds: List[KindVar] = List(),
    rtypes: List[TypeVar] = List(),
    suppressEscapes: Boolean = false
  )(
    f: Type => Type
  )(
    implicit hm: SubstEnv, su: Supply
  ): Type = alts match {
    case alt :: alts =>
      val pts = inferPatternTypes(g, alt.patterns)
      val li = alt.loc.inferred
      val sigmas = pts.extract
      val freepts = pts.xs.flatMap(v => ftvs(substType(VarT(v))))
      //TODO: Review whether this call was actually necessary:
      //val vsp = refreshList(Free, li, pts.vs)
      val vsp = pts.vs
      val expr = subTerm(zipTerms(pts.vs, vsp), alt.body)
      val tauz = inferType(vsp ++ g, expr, suppressEscapes)
      val (ks, tvs, qz, tau) = if (expr.isAnnotated) (List(),List(),Exists(li), tauz)
                               else unbind(Free,tauz)
      implicit val tml: Located = alt
      val tanns = freepts.map(v => substType(VarT(v))).toList
      val ptanns = tanns.filterNot(_.mono)
      if (ptanns nonEmpty) alt.die("error: unannotated parameters used polymorphically")
      unifyType(result, tau)
      val q = substType(qz)
      ts.zip(sigmas).foreach {
        case (t,sigma) => unifyType(substType(sigma), substType(t)); ()
      }
      checkSkolemEscape(pts.ss, rtypes ++ pts.xs, Some(substType(f(tau))), suppressEscapes)
      inferAltTypesPrime(l, g, alts, ts.map(substType(_)), substType(result), q :: qs, ks ++ rkinds ++ pts.xks, tvs ++ pts.xs ++ rtypes, suppressEscapes)(f)
    case List() =>
      implicit val tml: Located = l
      val r = generalize(substGamma(g), Exists(l.inferred,List(),qs.map(substType(_))), substType(f(result)))
      restrictKinds(rkinds)
      restrictTypes(rtypes)
      r
  }

  // infer the result type of an Alt given the types of what it is matching on
  def inferAltTypes(l: Loc, gz: Gamma, alts: List[Alt], ts: List[Type], suppressEscapes: Boolean=false)(f: Type => Type)(implicit hm: SubstEnv, su: Supply): Type = {
    val g = kindChecks(gz, ts, Star(l.inferred))
    val mess = ts.map(t => unbind(Free, substType(t))).toList
    val a = fresh[Kind](l.inferred, None, Free, Star(l.inferred))
    inferAltTypesPrime(l, g, alts, mess.map(_._4), VarT(a), List(), mess.flatMap(_._1), mess.flatMap(_._2), suppressEscapes) {
      t => Forall(l.inferred, List(), List(), Exists(l.inferred, List(), mess.map(_._3)), f(t))
    }
  }

  // the inferred type has kind star
  def inferPatternType(g: Gamma, e: Pattern)(implicit hm: SubstEnv, su: Supply): Patterned[Type] = {
    val li = e.loc.inferred
    implicit val tml: Located = e
    e match {
      case VarP(v) =>
        val (ks, ts, t) = unbindAnnot(g, v.extract)
        Patterned(t, List(v as t), ks, List(), ts)
      case StrictP(_,p) => inferPatternType(g, p)
      case LazyP(_,p)   => inferPatternType(g, p)
      case WildcardP(_) =>
        val v = fresh[Kind](li, None, Free, Star(li))
        Patterned(extract = VarT(v), xs = List(v))
      case LitIntP(_,i)     => Patterned(int at li)
      case LitByteP(_,i)    => Patterned(byte at li)
      case LitShortP(_,i)   => Patterned(short at li)
      case LitLongP(_,l)    => Patterned(long at li)
      case LitStringP(_, s) => Patterned(string at li)
      case LitCharP(_,c)    => Patterned(char at li)
      case LitFloatP(_,f)   => Patterned(float at li)
      case LitDoubleP(_,d)  => Patterned(double at li)
      case LitDateP(_,d)    => Patterned(date at li)
      case AsP(_,p1,p2) =>
        val pt1 = inferPatternType(g, p1)
        val pt2 = inferPatternType(g, p2)
        val t = substType(pt1.extract)
        unifyType(t, pt2.extract)
        (pt1 >> pt2) as substType(t)
      case ProductP(_,pats) =>
        val pts = inferPatternTypes(g, pats)
        val ts = pts.extract.map(substType(_)).toList
        pts as ProductT(li, ts.length)(ts:_*)
      case ConP(_,con,pats)    =>
        val pts = inferPatternTypes(g, pats)
        val ptau = unfurl(con.extract)
        val (sigmas, tau) = ptau.extract
        if (pts.extract.length != sigmas.length) e.die("error: expected constructor with " + ordinal(pts.extract.length,"argument","arguments"))
        sigmas.zip(pts.extract).foreach {
          case (sigma, pt) => unifyType(substType(pt), substType(sigma))
        }
        (pts >> ptau) as (substType(tau) at li)
    }
  }

  def reduce(lc: Loc,
             csz: List[Type],
             es: List[TypeVar],
             ps: List[Partition])(implicit hm: SubstEnv, su: Supply, tml: Located) =
    ps.foldRight(csz) {
      case (Partition(v, RHSConcr(fs), _), cs) =>
        instantiateType(v, ConcreteRho(lc, fs))
        cs.map(substType _)
      case (Partition(v, RHS(abs, con), _), cs) if v.ty.ambiguous || es.contains(v) =>
        cs map {
          case Part(loc, l, rs) => Part(loc, l, rs flatMap {
              case VarT(`v`) => ConcreteRho(lc, con) :: abs.toList.map(VarT(_))
              case x         => List(x)
            }
          )
          case x => x
        }
      case (_, cs) => cs
    }

  def solve(csz: Type)(implicit hm: SubstEnv, su: Supply, tml: Located): Type = {
    val l = csz.loc
    val (es, cs) = unbindExists(Ambiguous(Free), csz)
    val (q, esp) = PQueue.build(Exists(l, List(), cs))
    var ps = q.expand.toList
    Exists(l, List(), reduce(l, cs map (substType _), es, ps))
  }

  def trySolveOn(g: Gamma, ty: Type)(implicit hm: SubstEnv, su: Supply, tml: Located) = {
    val (ks, uvs, ex, t) = unbind(Free, ty)
    val (_, evs, cs) = Exists.unfurl(ex)
    val fevs = typeVars(cs) -- evs -- uvs
    if(fevs.toSet.isEmpty) {
      val csp = solve(ex.nf)
      generalize(substGamma(g), csp, substType(t))
    } else ty
  }

  // Split a type into the domain and codomain
//  def unfurl(vt: VarType, t: Type)(implicit su: Supply): Patterned[(List[Type], Type)] = t match {
//    case AppT(AppT(Arrow(_), a), b) => unfurl(vt, b) map { case (sigmas, tau) => (a :: sigmas, tau) }
//    case tz : Forall =>
//      val (ks, ts, cs, t) = unbind(vt, tz)
//      val qs = unfurl(vt, t)
//      Patterned((), List(), ks, ts, List(cs)) >> qs
//    case b => Patterned((List(),b))
//  }

  def unfurl(t: Type)(implicit su: Supply): Patterned[(List[Type], Type)] = t match {
    case AppT(AppT(Arrow(_), a), b)    => unfurl(b) map { case (sigmas, tau) => (a :: sigmas, tau) }
    case Forall(loc, ks, ts, cs, body) =>
      val qs = unfurl(body)
      qs.extract match {
        case (sigmas, tau) =>
          val tvs = typeVars(tau)
          val (parms, exts) = ts partition (tvs contains _)
          val rks = refreshList(Free, loc, ks)
          val frvs = refreshList(Free, loc, parms)
          val skvs = refreshList(Skolem, loc, exts)
          val km = (ks zip (rks map VarK)).toMap
          val tm = ((parms zip (frvs map VarT)) ++ (exts zip (skvs map VarT))).toMap
          qs >> Patterned((sigmas map (_ subst (km, tm)), tau subst (km, tm)),
                  List(), rks, skvs, frvs, List(cs subst (km, tm)))
      }
    case b                             => Patterned((List(), b))
  }

  // requires q : Constraint, q quantifies over no variables?, t : Star
  /**
   * This function computes a generalized version of a given type,
   * quantifying over the (truly) free variables in it. The Gamma is used
   * to determine which free variables are actually bound in outer scopes,
   * and should not be quantified over.
   *
   * q2 is expected to be a set of constraints.
   *
   * This will also appropriately handle the splitting of quantified variables
   * into forall for unambiguous variables and exists for variables that appear
   * only in constraints.
   */
  def generalize(g: Gamma, q2: Type, ty: Type)(implicit hm: SubstEnv, su: Supply, tml: Located): Type = {
    val (_, _, q1, t) = dequantify(ty)
    val li = t.loc.generalized
    val q = Exists(li, List(), List(q1, q2))
    val ks = (kindVars(t) -- kindVars(g)).filter(_.ty != Skolem).toList
    val gs = typeVars(g).toList
    val ts = (typeVars(t) -- gs).filter(_.ty != Skolem).toList
    val nks = refreshList(Bound, li, ks)
    val km = zipKinds(ks,nks)
    val nts = refreshList(Bound, li, subKind(km, ts))
    val tm = zipTypes(ts,nts)
    val cs = Exists.unfurl(q.subst(km,tm))._3
    val xs = (typeVars(cs) -- nts -- gs).filter(_.ty != Skolem).toList
    val nxs = refreshList(Ambiguous(Bound), li, xs)
    hm.remembered = hm.remembered map { case (k, (g, t, loc)) => (k, (Type.sub(km, tm, g), t.subst(km,tm), loc)) }
    Forall(li,nks,nts, mkSimplified(tml.loc,nxs,subType(zipTypes(xs,nxs),cs)), t.subst(km,tm))
  }

  def generalizeKind(d: Delta, k: Kind)(implicit su: Supply): KindSchema = {
    val ks = (kindVars(k) -- kindVars(d)).filter(_.ty != Skolem).toList
    val nks = refreshList(Bound, k.loc, ks)
    KindSchema(k.loc.generalized, nks, subKind(zipKinds(ks,nks), k))
  }

  type Maps = (Map[TypeVar, Type], Map[TermVar, TermVar])
  def subTypeMaps[A:HasTypeVars](m: Maps, a: A): A = subType(preserveLoc(m._1), a)
  def subTermMaps[A:HasTermVars](m: Maps, a: A): A = subTermEx(Map(), preserveLoc(m._1), preserveLoc(m._2), a)
  def appendMaps(p: Maps, q: Maps): Maps = (p._1 ++ q._1, p._2 ++ q._2)

  /**
   * Runs type checking/inference on a module.
   */
  def checkModule(termNames: Map[Name,TermVar], m: Module, cm: Maps)(implicit hm: SubstEnv, su: Supply): Maps = {
    val mod = m.name
    var maps = mapAccum_(cm, m.fields) { checkFieldStatement(mod, termNames) }
    maps = mapAccum_(maps, m.foreignData) { checkForeignData(mod) }
    maps = mapAccum_(maps, typeDefComponents(m.types)) { checkTypeDefComponent(mod) }
    maps = mapAccum_(maps, m.foreigns) {
      (cm, s) => s match {
        case ForeignFunctionStatement(loc, v, ty, _, _) => checkForeignTerm(mod)(cm, v, ty)
        case ForeignMethodStatement(loc, v, ty, _)      => checkForeignTerm(mod)(cm, v, ty)
        case ForeignValueStatement(loc, v, ty, _, _)    => checkForeignTerm(mod)(cm, v, ty)
        case ForeignConstructorStatement(loc, v, ty)    => checkForeignTerm(mod)(cm, v, ty)
        case ForeignSubtypeStatement(loc, v, ty)        => checkForeignTerm(mod)(cm, v, ty)
      }
    }
    maps = mapAccum_(maps, m.tables) {
      case (cm, TableStatement(loc, db, vs, ty)) => mapAccum_(cm, vs.map(_._2)) { checkForeignTerm(mod)(_, _, ty) }
    }

    val is = subTermMaps(maps, m.implicits).map(_.close)
    val es = subTermMaps(maps, m.explicits).map(_.close)
    val bs : List[Binding] = is ++ es

    assertTermClosed(bs, maps._2.keySet ++ bs.map(_.v))
    assertTypeClosed(bs)

    val (_, ds, terms) = inferBindingGroupTypes(m.loc, Nil, is, es, true)
    for (d <- ds)
      if (!d.isTrivialConstraint)
        d.die("non-trivial deferred constraint in top level binding")


    val mp = m.subTerm(terms)
    val pts = mp.privateTerms

    val buf = new ListBuffer[(TermVar,TermVar)]()
    terms.foreach {
      case (k,v) if pts.contains(v) => ()
      case (k,v)                    => buf += (v -> v.copy(name = Some(global(mp.name, v))))
    }
    (maps._1, maps._2 ++ buf.toMap)
  }

  def checkTypeDefComponent(module: String)(cm: Maps, tds: List[TypeDef])(implicit hm: SubstEnv, su: Supply): Maps = {
    val dvs = tds.map(_.v)
    val tdsp = subTypeMaps(cm, tds).map(_.closeWith(dvs))
    tdsp.foreach(assertTypeClosed(_))
    val ktds = inferTypeDefKindSchemas(tdsp)
    var conMap: Map[TypeVar, Type] = null
    val cons = ktds map {
      case (ks, DataStatement(l, v, kindArgs, typeArgs, cons)) =>
        v -> Con(l, global(module, v), new ConDecl { def desc = "data" }, ks)
      case (ks, TypeStatement(l, v, kindArgs, typeArgs, body)) =>
        v -> Con(l, global(module, v), new TypeAliasDecl(kindArgs, typeArgs, { subType(preserveLoc(conMap - v), body) }), ks)
      case (ks, ClassBlock(l, v, kindArgs, typeArgs, ctx, privates, body)) =>
        v -> Con(l, global(module, v), new ConDecl { def desc = "class" }, ks)
    }
    conMap = cons.toMap
    mapAccum_((cm._1 ++ conMap, cm._2), ktds.zip(cons)) {
      case (s, ((_, DataStatement(l, v, kindArgs, typeArgs, cons)), (_, con))) =>
        (s._1, s._2 ++ cons.map {
          case (es, v, fields) =>
            val g = global(module, v)
            v -> fresh(v.loc, Some(g), Bound,
                  Forall.mk(v.loc.inferred,
                            con.schema.forall,
                            typeArgs ++ es,
                            Exists(v.loc.inferred),
                            subTypeMaps(s,fields).foldRight(con(typeArgs.map(VarT(_)):_*))((x, y) =>
                              Arrow(v.loc.inferred,x,y))))
        })
      case (s, _) => s
    }
  }

  def checkFieldStatement(module: String, termNames: Map[Name,TermVar])(cm: Maps, fs: FieldStatement)(implicit hm: SubstEnv, su: Supply): Maps = {
    val ty = subTypeMaps(cm, fs.ty)
    val otyp = ty match { case Nullable(typ) => primTypes.get(typ) map (_.withNull) ; case _ => primTypes.get(ty) }
    if (!otyp.isDefined) ty.die(text("Invalid field type:") :+: text(ty.toString))
    val maps = fs.vs.map { case v =>
      val name = global(module, v)
      val tyCon = Con(v.loc.inferred, name, FieldConDecl(ty), Field(v.loc.inferred).schema)
      val tmv = fresh(v.loc, Some(tyCon.name), Bound, field(tyCon, ty))
      termNames.get(v.name.get) match {
        case None    => (Map(v -> tyCon), Map() : Map[TermVar,TermVar])
        case Some(u) => (Map(v -> tyCon), Map(u -> tmv))
      }
    }
    maps.foldLeft(cm)(appendMaps)
  }

  // @throws Death
  def assertTermClosed[A:HasTermVars](t: A, ex: Set[TermVar] = Set()) {
    val ftmvs = termVars(t) -- ex
    if (ftmvs nonEmpty) die(vsep(ftmvs.map(v => v.report("error: undefined term")).toList))
  }

  // @throws Death
  def assertTypeClosed[A:HasTypeVars](t: A, ex: Set[TypeVar] = Set()) {
    val ftvs = typeVars(t) -- ex
    if (ftvs nonEmpty) die(vsep(ftvs.map(v => v.report("error: undefined type")).toList))
  }

  // @throws Death
  def assertKindClosed[A:HasKindVars](t: A, ex: Set[KindVar] = Set()) {
    val fkvs = implicitly[HasKindVars[A]].vars(t) -- ex
    if (fkvs nonEmpty) die(vsep(fkvs.map(v => v.report("error: undefined kind")).toList))
  }

  // @throws Death
  def checkForeignTerm(module: String)(cm: Maps, v: TermVar, t: Type)(implicit hm: SubstEnv, su: Supply): Maps = {
    val ty = subTypeMaps(cm, t).close
    implicit val loc: Located = ty
    kindCheck(Nil, ty, Star(ty.loc.inferred))
    val typ = substType(ty)
    assertTypeClosed(typ)
    (cm._1, cm._2 + (v -> fresh(v.loc, Some(global(module, v)), Bound, typ)))
  }

  // @throws Death
  def checkForeignData(module: String)(cm: Maps, fds: ForeignDataStatement): Maps = fds match {
    case ForeignDataStatement(loc, v, vs, clazz) =>
      val k = vs.foldRight(Star(loc.inferred) : Kind)((u, r) => ArrowK(loc.inferred, u.extract, r))
      val c = Con(loc, global(module, v), TypeConDecl(clazz.cls, true), k.schema)
      (cm._1 + (v -> c), cm._2)
  }

  // @throws Death
  def global(m: String, v: V[Any]): Global = v.name match {
    case Some(l : Local)                   => l global m
    case Some(g : Global) if g.module == m => g
    case _                                 => v.die("error: expected local name")
  }

  /*
   * Simplifies a constraint set to eliminate superfluous constra.
   * Uses the following heuristics:
   *
   * 1) Eliminate all but one permutation of a right hand side for
   *    partitions of a given variable. I.E.:
   *
   *      x <- Foo, y, Bar
   *      x <- Bar, Foo, y
   *
   * 2) Rules about existential variables are only useful inasmuch as
   *    they provide information about universal variables, so any
   *    rules that aren't transitively related to universal variables
   *    should be eliminated.
   *
   *      forall a. (exists w x y z. a <- (Foo,w), x <- (Bar,y), z <- (Bar,w)). ...
   *
   *    can be simplified to:
   *
   *      forall a. (exists w z. a <- (Foo,w), z <- (Bar, w)). ...
   */
  private case class NormalPart(loc: Loc, left: TypeVar, concrete: Set[Name], abstrakt: List[TypeVar]) {
    override def equals(a: Any) = a match {
      case NormalPart(_, l, c, a) => l == left && c == concrete && a.sortWith(_.id < _.id) == abstrakt.sortWith(_.id < _.id)
    }
    def part: Type = Part(loc, VarT(left), ConcreteRho(loc, concrete) :: abstrakt.map(VarT(_)))
  }

  def mkSimplified(l: Loc, exts: List[TypeVar], ps: List[Type])(implicit hm: SubstEnv, su: Supply, tml: Located): Type = {
    def isolated(acc: Set[TypeVar], parts: List[Type]): Set[TypeVar] = {
      val dirty = parts.foldLeft(Set[TypeVar]()) {
        case (d,p) =>
          val pvs = typeVars(p).toSet
          val dvs = pvs -- acc
          if(dvs.isEmpty) d else d ++ pvs.intersect(acc)
      }

      if(dirty.isEmpty) acc else isolated(acc -- dirty, parts)
    }
    def normalPart(t: Type): Option[Either[NormalPart,Type]] = t match {
      case p@Part(loc, l, rs) =>
        val (cs,vs,ts) = rs.foldLeft((Set[Name](),List[TypeVar](),List[Type]())) {
          case ((cs, vs, ts), VarT(v))           => (cs, v :: vs, ts)
          case ((cs, vs, ts), ConcreteRho(_, s)) =>
            val i = cs.intersect(s)
            if(i.nonEmpty)
              l.die("Fields appear twice in row: " + i.mkString(","))
            else (cs ++ s, vs, ts)
          case ((cs, vs, ts), c@Con(_, n, _, _)) => (cs + n, vs, ts)
          case ((cs, vs, ts), t)                 => (cs, vs, t :: ts)
        }
        if(!ts.isEmpty) Some(Right(p)) // There's something we don't know how to deal with
        else l match {
          case ConcreteRho(loc, s) =>
            if(vs.isEmpty && cs == s) None
            else if(cs.isEmpty && vs.length == 1) Some(Left(NormalPart(loc, vs.head, s, List())))
            else Some(Right(p))
          case VarT(v) =>
            Some(Left(NormalPart(loc, v, cs, vs)))
          case _ => Some(Right(p))
        }
      case p => Some(Right(p))
    }
    val iso = isolated(exts.toSet, ps)
    val (classes, parts) = ps.partition(_.isClassConstraint)
    val (unknown, normal) = parts.map(normalPart).collect({ case Some(p) => p }).partition(_.isRight)
    val (dumb, extinct) = (normal.distinct.map(_.left.get.part) ++ unknown.map(_.right.get)).partition {
      p => (typeVars(p).toSet -- iso).nonEmpty
    }
    // solve constraints before throwing them away to ensure failure for unsatisfiable sets
    solve(Exists(l, List(), extinct))
    val complex = reduce(classes)
    val am = ambiguitiesIn(exts, complex).map(_.v).toSet
    val lessComplex = complex.filterNot(p => typeVars(p).exists(am))
    val pruned = lessComplex ++ dumb
    Exists(l, exts filterNot (v => iso(v) || am(v)), pruned)
  }
}
