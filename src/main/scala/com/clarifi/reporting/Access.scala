package com.clarifi.reporting
/*
import scalaz.{@@, Equal, Monoid, NonEmptyList, Show, Tag}
import scalaz.Id.Id
import scalaz.Tags.Disjunction
import scalaz.syntax.equal._
import scalaz.syntax.show._
import scalaz.syntax.id._
import scalaz.syntax.monad._
import scalaz.syntax.monoid._
import scalaz.syntax.std.all.ToTuple2Ops
import scalaz.syntax.std.list._
import scalaz.std.either._
import scalaz.std.map.{mapKeys, unionWith}
import scalaz.std.option._
import scalaz.std.string._

import util.{Clique, Edge, Keyed, PartitionedSet}
import Reporting._
import ReportingUtils.foldNel
import RelationImpl.Ref

import Provenance.RefUsage

/** From whence the data in a relation has come.  Typically, you
  * should extract a final result with `references`, rather than
  * destructuring.
  *
  * @tparam Col The key type in the column graph.
  *
  * @param consts records that e.g. of table `Blah`, we use only that
  * part for which `x=1` and `y=42`, or perhaps that part for which
  * `p=q`.
  *
  * @param related records two-way relations between fields, such as
  * those created by a join.  Data propagation is unordered, so a↔b↔c
  * ⇒ a↔c.
  */
case class Provenance[Col](private val consts: Reflexivity[Col],
                           private val related: PartitionedSet[Col])
     extends Keyed[Provenance, Col] {
  /** Answer what parts of relations — both field-wise and value-wise
    * — were accessed to yield the resulting relation. */
  def references(th: Header)(implicit bc: Col =:= BackedColumn): RefUsage = {
    val orgConsts = (consts.propagate(c => bc(c) match {
                       case bc@AbsCol(_, _) => Iterable(bc)
                       case _ => Iterable.empty})
                     .group(_.uref)(_.col)
                     withDefaultValue Reflexivity.zero[ColumnName])
    // Right reachables
    (reachable(th.keySet) collect {case ac@AbsCol(_, _) => ac}
     groupBy (_.uref) mapValues (_ map (_.col) toSet)) map {
       case (urf, cols) => (urf, (cols, orgConsts(urf)))
    }
  }

  /** Answer columns, concrete and derived, reachable from relation
    * `cols`. */
  def reachable(cols: Set[ColumnName])(implicit bc: Col =:= BackedColumn
                                     ): Set[BackedColumn] =
    related inj bc exclusive Clique(cols map RelCol)

  /** Filter relational columns. */
  def project(p: ColumnName => Boolean)(implicit bc: Col =:= BackedColumn
                                     ): Provenance[Col] =
    filterKeys(c => bc(c) match {case RelCol(col) => p(col)
                                case AbsCol(_, _) => true})

  override def inj[B](f: Col => B): Provenance[B] =
    Provenance(consts inj f, related inj f)

  def propagate[B](f: Col => Iterable[B]): Provenance[B] =
    Provenance(consts propagate f, related propagate f)

  def replaceKeys(ren: PartialFunction[Col, Col]): Provenance[Col] =
    Provenance(consts replaceKeys ren, related replaceKeys ren)
}

/** Tag a Relation with Hs and `Provenance`. */
class RAccess[H](implicit htag: RTag[H]) extends RTag[(Provenance[BackedColumn], H)] {
  import RAccess._
  type Tag = (Provenance[BackedColumn], H)
  @inline private[this] def pr(t: Tag) = t._1
  @inline private[this] def h(t: Tag) = t._2
  // Supporting the transient pattern used in some of the methods.
  private type TransientBC = Either[BackedColumn, BackedColumn]
  @inline private def bcL(bc: BackedColumn): TransientBC = Left(bc)
  @inline private def bcR(bc: BackedColumn): TransientBC = Right(bc)
  private def provenance(consts: Reflexivity[BackedColumn],
                         related: PartitionedSet[BackedColumn]) =
    Provenance(consts, related)

  /** @todo SMRC a reasonable improvement to the graphing of
    *       multi-sourced Refs would be to introduce automatic
    *       partitioning of AbsCols into BackedColumn and
    *       Provenance. */
  def ref(id: => RefID, t: => Header, s: => Source): Tag = {
    val me = UntypedRef(id, s)
    // bind concrete columns to the relational namespace
    val equiv = PartitionedSet(t.keys map (coln =>
      Clique[BackedColumn](Set(RelCol(coln), AbsCol(me, coln)))))
    provenance(ForallTups(Map.empty, equiv),
               equiv) -> htag.ref(id, t, s)
  }

  // While there may seem to be no provenance information in a
  // literal, the constancies we gather can be essential;
  // e.g. someTable & [{x = 1}]
  def literal(atoms: NonEmptyList[Tuple]): Tag =
    provenance(Reflexivity literal atoms inj RelCol,
               PartitionedSet.zero) -> htag.literal(atoms)

  def empty(ts: Header): Tag =
    provenance(KnownEmpty(), PartitionedSet.zero) -> htag.empty(ts)

  def join(a1: Tag, a2: Tag): Tag =
    provJoinOn(pr(a1), pr(a2), (toHeader(a1).keySet & toHeader(a2).keySet)
               map (k => (k, k))) -> htag.join(h(a1), h(a2))

  private def provJoinOn(pv1: Provenance[BackedColumn],
                         pv2: Provenance[BackedColumn],
                         on: Set[(ColumnName, ColumnName)]
                       ): Provenance[BackedColumn] = {
    def absConnections(elts: Set[TransientBC]) =
      (elts filter (whichever(_).isAbs)
       groupBy whichever).values map Clique.apply
    val Provenance(aConsts, aRelated) = pv1 inj bcL
    val Provenance(bConsts, bRelated) = pv2 inj bcR
    val lefts = on map (_._1)
    // cliques to connect the `on`s
    val equiv = PartitionedSet(on.toIterable map {
      case (l, r) => Clique(Set(bcL(RelCol(l)), bcR(RelCol(r))))
    })
    val jConsts = aConsts && bConsts && ForallTups(Map.empty, equiv)
    val jRelated = aRelated allow bRelated allow equiv
    Provenance(// colliding equivs must be erased
               jConsts filterKeys (absConnections(jConsts.elements)
                                   filter (!jConsts.equivalent(_))
                                   flatMap (_.value) toSet).andThen(!_),
               // colliding AbsCols need to form self-edges
               jRelated allow
               PartitionedSet(absConnections(jRelated.elements))) injColl {
      // left side wins in a collision
      case Right(v@RelCol(col)) if !lefts(col) => v
      case Left(v) => v
    }
  }

  def joinOn(a1: Tag, a2: Tag, on: Set[(String, String)]): Tag =
    provJoinOn(pr(a1), pr(a2), on) -> htag.joinOn(h(a1), h(a2), on)

  def union(a1: Tag, a2: Tag): Tag =

    (pr(a1) |+| pr(a2)) -> htag.union(h(a1), h(a2))

  def minus(a1: Tag, a2: Tag): Tag =
    (pr(a1) |+| pr(a2)) -> htag.minus(h(a1), h(a2))

  /** @todo SMRC could do better here with `related` being a directed
    *       graph */
  def filter(a: Tag, p: Predicate): Tag = {
    val Provenance(consts, related) = pr(a)
    provenance(consts && (Predicates constancies p inj RelCol),
               related invite Clique(toHeader(a).keySet map RelCol)) ->
      htag.filter(h(a), p)
  }

  def project(a: Tag, ts: Set[String]): Tag =
    (pr(a) project ts) -> htag.project(h(a), ts)

  private def combineAll[K: Equal](pv: Provenance[K], unsimplComb: Map[K, Op]
                                 )(opevalenv: PartialFunction[K, ColumnName],
                                   boxcol: ColumnName => K): Provenance[K] = {
    val Provenance(consts, related) = pv
    val evalEnv = consts.consts collect {
      case (col, Some(v)) if opevalenv isDefinedAt col =>
        (opevalenv(col), Op.OpLiteral(v))
    }
    val comb = unsimplComb mapValues (_ simplify evalEnv)
    type Transient = Either[K, K]
    Provenance(consts combineAll (comb, opevalenv, boxcol),
               related inj (Left(_): Transient)
               allow PartitionedSet(comb map {case (cod, op) =>
                 Clique((op.columnReferences
                         map (boxcol andThen (Left(_): Transient)))
                        + Right(cod))
               }) injColl {case Left(v) if !(comb isDefinedAt v) => v
                           // right side wins in a collision
                           case Right(v) => v})
  }

  def combine(a: Tag, codomain: Attribute, op: Op): Tag =
    combineAll(pr(a), Map((RelCol(codomain.name): BackedColumn) -> op)
             )({case RelCol(col) => col}, RelCol) ->
      htag.combine(h(a), codomain, op)

  def aggregate(a: Tag, codomain: Attribute, func: AggFunc): Tag = {
    def colrefs(o: Op) = o.columnReferences
    val Attribute(attName, _) = codomain
    val Provenance(consts, related) = pr(a)
    provenance(consts filterKeys (_.isAbs),
               related invite Clique((func(count = toHeader(a).keySet,
                                           sum = colrefs, avg = colrefs,
                                           min = colrefs, max = colrefs,
                                           stddev = colrefs, variance = colrefs)
                                      + attName) map RelCol)) ->
      htag.aggregate(h(a), codomain, func)
  }

  def rename(a: Tag, t1: String, t2: String): Tag =
    pr(a).replaceKeys(Map(RelCol(t1) -> RelCol(t2))) -> htag.rename(h(a), t1, t2)

  def limit(a: Tag, from: Option[Int], to: Option[Int],
            order: List[(String, SortOrder)]): Tag =
    pr(a) -> htag.limit(h(a), from, to, order)

  def amalgamate(as: List[Tag], proj: Set[ColumnName],
                 ren: Map[ColumnName, ColumnName],
                 comb: Map[Attribute, Op],
                 filt: Predicate): Tag = {
    assume(as.nonEmpty)
    val combKeys = comb.keySet map (_.name)
    (combineAll(filter(foldNel(as.toNel.get)(join), filt)._1
                propagate (c => Iterable(bcL(c), bcR(c)))
                filterKeys {case Left(RelCol(rc)) => proj(rc)
                            case _ => true}
                replaceKeys {case Left(RelCol(rc))
                             if ren isDefinedAt rc => bcL(RelCol(ren(rc)))},
                mapKeys(comb)(cn => bcR(RelCol(cn.name)))
              )({case Right(RelCol(cn)) => cn}, cn => bcR(RelCol(cn)))
     injColl {case Left(c@RelCol(rc)) if !combKeys(rc) => c
              case Right(c@RelCol(rc)) if combKeys(rc) => c
              case Right(c@AbsCol(_, _)) => c: BackedColumn}) ->
      htag.amalgamate(as map h, proj, ren, comb, filt)
  }

  def toHeader(a: Tag): Header = htag toHeader h(a)
}

object RAccess {
  private[RAccess] def whichever[B](e: Either[B, B]): B =
    e fold (identity, identity)
}

/** A `Ref` stripped of its type information. */
final case class UntypedRef(refid: RefID, source: Source) {
  import UntypedRef._
  def identifies(r: Ref) = this === UntypedRef(r)
}

object UntypedRef extends (Ref => UntypedRef) {
  def apply(r: Ref): UntypedRef =
    r match {case Ref(r, _, s) => UntypedRef(r, s)}

  implicit val UntypedRefEqual: Equal[UntypedRef] =
    Equal.equal((a, b) => a.refid === b.refid && a.source === b.source)

  implicit val UntypedRefShow: Show[UntypedRef] =
    Show.shows({case UntypedRef(rid, src) =>
      "UntypedRef(%s,%s)" format (rid.shows, src.shows)})
}

/** A relational or concrete column. */
sealed abstract class BackedColumn {
  def isRel = this match {case _: RelCol => true; case _ => false}
  def isAbs = this match {case _: AbsCol => true; case _ => false}
}
private[reporting] case class RelCol(col: ColumnName) extends BackedColumn
private[reporting] case class AbsCol(uref: UntypedRef, col: ColumnName)
                        extends BackedColumn

object BackedColumn {
  implicit val EqualBC: Equal[BackedColumn] = Equal.equalA
  implicit val ShowBC: Show[BackedColumn] = Show.showA
}

object Provenance {
  /** Result of `Provenance#references`. */
  type RefUsage = Map[UntypedRef, (Set[ColumnName], Reflexivity[ColumnName])]

  object RefUsage {
    type Union = RefUsage @@ Disjunction

    /** Unbox. */
    @inline final def data[T](x: RefUsage @@ T): RefUsage =
      Tag.unsubst[RefUsage, Id, T](x)

    implicit val refUsageUnionMonoid: Monoid[Union] = new Monoid[Union] {
      def zero = Disjunction(Map.empty)
      def append(l: Union, r: => Union) =
        Disjunction(unionWith(data(l), data(r)){
          (ad, bd) => (ad, bd) match {
            case ((as, ar), (bs, br)) =>  (as | bs, ar || br)}})
    }

    /** Answer whether `allowed` is sufficient to access
      * `required`. */
    def permitted(allowed: RefUsage, required: RefUsage): Boolean =
      difference(required, allowed).isEmpty

    private[this] def mapDifference[K, V, V1 <: V, V2 <: V
                                  ](l: Map[K, V1], r: Map[K, V2]
                                  )(join: (V1, V2) => Option[V]) : Map[K, V] =
      l flatMap {case en@(k, v) => r.get(k) match {
        case None => Seq(en)
        case Some(rv) => join(v, rv).toSeq map (k ->)}}

    /** Subtract `small` from `big`. */
    def difference(big: RefUsage, small: RefUsage): Map[UntypedRef, Set[ColumnName]] =
      mapDifference(big, small){(l, r) => (l, r) match {
        case ((bcols, brx), (scols, srx)) =>
          val aligned = (scols -- srx.consts.filter{case (sk, sv) =>
            !sv.isDefined || (sv /== brx.consts.get(sk).join)}.keys)
          Some(bcols &~ aligned) filter (_ nonEmpty) map (_ -> brx) // brx will be ignored
      }} mapValues (_._1)
  }

  /** Decoration that infers required source capabilities. */
  implicit def accessing[H: RTag]: RTag[(Provenance[BackedColumn], H)] = new RAccess

  def zero = mzero[Provenance[BackedColumn]]

  /** The safe monoid of `Provenance`, where append introduces no new
    * relationships. */
  implicit val ProvenanceMonoid: Monoid[Provenance[BackedColumn]] = new Monoid[Provenance[BackedColumn]] {
    /** Derives no data from concrete sources. */
    val zero = Provenance[BackedColumn](Reflexivity.zero, PartitionedSet.zero)

    /** Derives data from `a` and `b` without relating them. */
    def append(a: Provenance[BackedColumn], b: => Provenance[BackedColumn]) = {
      val (Provenance(aConsts, aRelated),
           Provenance(bConsts, bRelated)) = (a, b)
      // Neither a simple Reflexivity && or || is appropriate.  If
      // aConsts talks only about tableX, and bConsts about tableY,
      // the lack of const info in bConsts about tableX shouldn't
      // suppress that of aConsts.
      def splitConsts(rx: Reflexivity[BackedColumn]
                    ): Map[UntypedRef, Reflexivity[BackedColumn]] = rx match {
        case KnownEmpty() => Map.empty
        case ForallTups(consts, equiv) =>
          val split = consts groupBy {case (RelCol(cn), _) => None
                                      case (AbsCol(rf, _), _) => Some(rf)}
          split collect {case (Some(ur), urcts) =>
            ur -> ForallTups(urcts ++ split.getOrElse(None, Map.empty), equiv)}
      }
      val rx = ((Iterable(bConsts.filterKeys(_.isRel)
                          || aConsts.filterKeys(_.isRel)) ++
                 unionWith(splitConsts(bConsts),
                           splitConsts(aConsts))(_ || _).values)
                /:\ Reflexivity.zero)(_ && _)
      Provenance(rx, bRelated | aRelated)
    }
  }

  implicit def ProvenanceShow[Col: Show]: Show[Provenance[Col]] = Show.shows({
    case Provenance(consts, related) =>
      "Provenance(%s,%s)" format (consts.shows, related.shows)})
}
*/
