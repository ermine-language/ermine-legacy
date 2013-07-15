package com.clarifi.reporting.util

import collection.immutable.{LinearSeq, SortedSet}

import scalaz.{Equal, Functor, Monoid, Order, Show}
import scalaz.syntax.id._
import scalaz.syntax.monoid._
import scalaz.syntax.order._
import scalaz.syntax.show._
import scalaz.syntax.std.all.ToTuple2Ops
import scalaz.std.map.mapKeys
import scalaz.std.option._
import scalaz.std.set._


case class Clique[A](value: Set[A]) {
  /** Apply an injection to myself. */
  def inj[B](f: A => B): Clique[B] = Clique(value map f)
}

/** A set of disjoint sets.
  *
  * @note XXX Equality is quite slow; try not to use it.
  *
  * @todo SMRC require, allow, et al could probably do less */
class PartitionedSet[A](private val posns: Map[A, Long],
                        private val tick: Long)
      extends Equals with Keyed[PartitionedSet, A] {
  import PartitionedSet._
  assert(tick <= maxTick)

  private lazy val byId: Map[Long, Set[A]] =
    posns.toIterable groupBy (_._2) mapValues (_ map (_._1) toSet)

  /** Answer my elements in no particular order. */
  def elements: Set[A] = posns.keySet

  /** Reinterpret each subset as a `Clique`. */
  def cliques: Iterable[Clique[A]] = byId.values map Clique.apply

  /** Reinterpret as an undirected graph.
    *
    * @note ∀a∈A. `graph(a).nonEmpty = elements(a)` */
  def graph: A => Set[A] = {
    val ids = byId withDefaultValue Set.empty
    (a: A) => posns.get(a) map ids getOrElse Set.empty
  }

  /** Apply an injection to myself. */
  override def inj[B](f: A => B): PartitionedSet[B] =
    PartitionedSet(mapKeys(posns)(f), tick)

  /** Apply an inverse function to myself.
    *
    * @note invariant: values of `f` are disjoint for different inputs */
  def propagate[B](f: A => Iterable[B]): PartitionedSet[B] =
    PartitionedSet(posns flatMap {case (el, id) => f(el) map (_ -> id)}, tick)

  /** Like `inj`, but partial, and overwrite anything in my domain
    * with `ren`'s range. */
  def replaceKeys(ren: PartialFunction[A, A]): PartitionedSet[A] = {
    val (renamed, unrenamed) = posns partition (ren isDefinedAt _._1)
    PartitionedSet(unrenamed ++ mapKeys(renamed)(ren), tick)
  }

  /** Filter my `A`s. */
  override def filterKeys(p: A => Boolean) =
    PartitionedSet(posns filterKeys p, tick)

  /** Regroup.
    *
    * @note `fa <|*|> fb` must form an injection. */
  def group[B, C](fb: A => B)(fc: A => C): Map[B, PartitionedSet[C]] =
    (posns groupBy (_._1 |> fb)
     mapValues {ss => PartitionedSet(mapKeys(ss)(fc), tick)})

  /** Answer whether xs is a subclique. */
  def contains(xs: Iterable[A]): Boolean = {
    val ids = xs.view map posns.lift
    (ids.headOption map {h => h.isDefined && ids.forall(h ===)}
     getOrElse true)
  }

  /** Edge-set and element intersection. */
  def require(other: PartitionedSet[A]): PartitionedSet[A] = {
    val lg = graph
    val rg = other.graph
    @annotation.tailrec
    def rec(left: Set[A], cliques: List[Clique[A]]): Iterable[Clique[A]] =
      if (left.isEmpty) cliques
      else {
        val pivot = left.head
        val captured = lg(pivot) & rg(pivot)
        rec(left - pivot &~ captured,
            if (captured.isEmpty) cliques else Clique(captured) :: cliques)
      }
    PartitionedSet(rec(elements & other.elements, Nil))
  }

  /** Edge-set and element intersection. */
  @inline final def &(other: PartitionedSet[A]) = require(other)

  /** Edge-set and element union. */
  def allow(other: PartitionedSet[A]): PartitionedSet[A] = {
    val linked = other.cliques filter (_.value & elements nonEmpty)
    (PartitionedSet(posns ++
                    ((other.posns -- linked.flatMap(_.value))
                     mapValues (tick +)),
                    tick + other.tick)
     /: linked){case (ps, c) => ps invite c}
  }

  /** Edge-set and element union. */
  @inline final def |(other: PartitionedSet[A]) = allow(other)

  /** Edge intersection with element union. */
  def sparse(other: PartitionedSet[A]): PartitionedSet[A] = {
    val lg = graph
    val rg = other.graph
    @annotation.tailrec
    def rec(left: Set[A], cliques: List[Clique[A]]): Iterable[Clique[A]] =
      if (left.isEmpty) cliques
      else {
        val pivot = left.head
        val captured = (lg(pivot) & rg(pivot)) + pivot
        rec(left &~ captured, Clique(captured) :: cliques)
      }
    PartitionedSet(rec(elements | other.elements, Nil))
  }

  /** Join `c`.  Subsets with connections to `c` end up in one subset
    * alongside `c`'s members. */
  def invite(c: Clique[A]): PartitionedSet[A] = elements & c.value match {
    case common if common.nonEmpty =>
      val joiningIds = common map posns
      val joinedId = joiningIds.head
      PartitionedSet(posns.mapValues{case j if joiningIds(j) => joinedId
                                     case nj => nj}
                     ++ c.value.toIterable.map(_ -> joinedId), tick)
    case _ => PartitionedSet(posns ++ c.value.toIterable.map(_ -> tick),
                            tick + 1)
  }

  /** Collect all cliques that belong with `key`, non-transitively.
    *
    * @note ∃ps,ps2,k. `ps2 exclusive (ps exclusive k)`
    *                  ≠ `(ps |+| ps2) exclusive k` */
  def exclusive(key: Clique[A]): Clique[A] = elements & key.value match {
    case common if common.nonEmpty =>
      val joiningIds = common map posns
      Clique(key.value ++ posns.collect{case (elt, i) if joiningIds(i) => elt})
    case _ => key
  }

  def canEqual(o: Any) = o.isInstanceOf[PartitionedSet[_]]
  override def equals(o: Any) = o match {
    case o: PartitionedSet[_] if o canEqual this =>
      elements == o.elements && cliques.toSet == o.cliques.toSet
    case _ => false
  }
  override def hashCode = elements.hashCode

  override def toString = "PartitionedSet(" + cliques + ")"
}

object Clique {
  /** Auto-unbox. */
  @inline final implicit def ToSet[A](cq: Clique[A]): Set[A] = cq.value

  implicit def CliqueShow[A: Show]: Show[Clique[A]] = Show.shows(cq =>
    cq.value.toSeq.map(_.shows).mkString("Clique(", ",", ")"))

  implicit def CliqueOrder[A: Order]: Order[Clique[A]] = new Order[Clique[A]] {
    def order(l: Clique[A], r: Clique[A]) =
      l.value ?|? r.value
    override def equal(l: Clique[A], r: Clique[A]) =
      l.value === r.value
    override def equalIsNatural = Equal[A].equalIsNatural
  }

  implicit def CliqueMonoid[A]: Monoid[Clique[A]] = new Monoid[Clique[A]] {
    val zero = Clique(Set.empty[A])
    def append(a: Clique[A], b: => Clique[A]) = Clique(a | b)
  }
}

object PartitionedSet {
  /** Merging is easier to manage by splitting the number space, and
    * letting `renumber` manage fitting into that space.  That split
    * may cause normalization to happen more often then you might
    * think, though we assume that `PartitionedSet`s with
    * 4,611,686,018,427,387,902 elements are impractical. */
  private[PartitionedSet] val maxTick: Long = java.lang.Long.MAX_VALUE / 2 - 1

  /** Renumber a `posns` for tick conservation. */
  private[this]
  def renumber[A](posns: Map[A, Long]): (Map[A, Long], Long) = {
    val nums = (SortedSet.empty[Long] ++ posns.values).toIndexedSeq
    @annotation.tailrec
    def rec(rewrite: Map[Long, Long], tick: Long,
            here: Int, there: Int): (Map[Long, Long], Long) = () match {
      case _ if here >= there => (rewrite, tick)
      case _ if tick < nums(here) =>
        rec(rewrite + (nums(there) -> tick), tick + 1, here, there - 1)
      case _ => rec(rewrite, tick + 1, here + 1, there)
    }
    rec(Map.empty, 0, 0, nums.size - 1) fold {(renum, tick) =>
      (posns mapValues (renum withDefault identity), tick)
    }
  }

  /** Normalize a prepared `PartitionedSet`. */
  private[PartitionedSet]
  def apply[A](posns: Map[A, Long], tick: Long): PartitionedSet[A] = tick match {
    case toobig if toobig > maxTick =>
      renumber(posns) fold (new PartitionedSet(_, _))
    case tick => new PartitionedSet(posns, tick)
  }

  /** Build a partitioned set from cliques.  We assume that all of
    * `cliques` are disjoint. */
  def apply[A](cliques: Iterable[Clique[A]]): PartitionedSet[A] =
    PartitionedSet(cliques.zipWithIndex
                   flatMap {case (cq, id) => cq.value map (_ -> (id: Long))}
                   toMap, cliques.size)

  /** Build a partitioned set from a single clique. */
  def single[A](as: A*): PartitionedSet[A] =
    PartitionedSet(Iterable(Clique(Set(as: _*))))

  def zero[A] = mzero[PartitionedSet[A]]

  /** Treat each of `edges` as a clique membership marker. */
  def fromEdges[A](edges: Iterable[Edge[A]]): PartitionedSet[A] =
    (zero[A] /: edges){case (cqs, e) => cqs invite Clique(Set(e._1, e._2))}

  /** Clique-merging monoid, where zero has no cliques. */
  implicit def PartitionedSetMonoid[A]: Monoid[PartitionedSet[A]] =
    new Monoid[PartitionedSet[A]] {
      val zero = PartitionedSet(Map.empty[A, Nothing], 0)
      def append(a: PartitionedSet[A], b: => PartitionedSet[A]) = b allow a
    }

  implicit def PartitionedSetEqual[A: Order]: Equal[PartitionedSet[A]] =
    if (Order[A].equalIsNatural) Equal.equalA
    else Equal equal ((l, r) =>
      l.elements === r.elements && l.cliques.toSet === r.cliques.toSet)

  implicit def PartitionedSetShow[A: Show]: Show[PartitionedSet[A]] =
    Show.shows(ps => "PartitionedSet(" + ps.cliques.map(_.shows).mkString(",") + ")")
}

/** A two-valued bag. */
class Edge[+A](l: A, r: A) extends Product2[A, A] {
  val _1 = if (l.## <= r.##) l else r
  val _2 = if (l.## <= r.##) r else l

  def contains[B >: A](it: B)(implicit ev: Equal[B]) = it === _1 || it === _2

  def canEqual(o: Any) = o.isInstanceOf[Edge[_]]
  override def equals(o: Any) = o match {
    case o: Edge[_] if o.canEqual(this) =>
      _1 == o._1 && _2 == o._2
    case _ => false
  }
  override def hashCode = (_1, _2).hashCode
}

object Edge {
  def apply[A](l: A, r: A) = new Edge(l, r)

  // nb. ∃a,b ∈ A. unapply(Edge(a,b)).get = Product2(b,a)
  def unapply[A](e: Edge[A]) = Product2 unapply e

  implicit def EdgeEqual[A: Equal]: Equal[Edge[A]] =
    Equal.equal((a, b) => a._1 === b._1 && a._2 === b._2)

  private[this] def ordered[A: Order](edge: Edge[A]): Product2[A, A] =
    if (edge._1 lte edge._2) edge else (edge._2, edge._1)

  implicit def EdgeOrder[A: Order]: Order[Edge[A]] =
    Order.order{(a, b) =>
      // The order we pick for _1, _2 isn't compatible with the
      // Order laws.  So we reorder first
      val Product2(a1, a2) = ordered(a)
      val Product2(b1, b2) = ordered(b)
      a1 ?|? b1 |+| a2 ?|? b2
    }

  /** Edges are not traversable, because reordering may e.g. cause
    * `e.map(f).sequence` to yield a different applicative order than
    * `e.traverse(f)`.  They also violate the composition law of
    * Applicative. */
  implicit val EdgeFunctor: Functor[Edge] = new Functor[Edge] {
    def map[A, B](a: Edge[A])(f: A => B) = Edge(f(a._1), f(a._2))
  }

  /** Build a bidirectional graph from an edge set. */
  def undirectedGraph[A](eds: Traversable[Edge[A]]): Map[A, Set[A]] =
    (eds flatMap {case e@Product2(a, b) => Seq(e, (b -> a))}
     groupBy (_._1) mapValues (_ map (_._2) toSet))
}

object Graph {
  /** Answer nodes reachable in graph `g` from `roots`, including
    * `roots`. */
  def reachable[A](roots: LinearSeq[A], g: A => Set[A]): Set[A] = {
    @annotation.tailrec
    def walk(q: LinearSeq[A], acc: Set[A]): Set[A] =
      q.headOption map (_ |> g diff acc) match {
        case None => acc
        case Some(xs) => walk(xs ++: q.tail, acc ++ xs)
      }
    walk(roots, roots.toSet)
  }
}
