package com.clarifi.reporting
package ermine

/*
 * This module handles the constraint solving for row types in
 *
 * After much consideration, we decided that the necessary constraints for
 * our row types could be collapsed into a single one: partitioning. Here,
 * partitioning will be denoted <-. First some rules and conventions:
 *
 * 1) Only single variables may appear to the left of a partition.
 * 2) Variables are written lowercase: a, b, c, x, y, z
 * 3) Field constants are written uppercase: C, D, E, F
 * 4) Said field constants are equivalent to singleton rows: C denotes (| C |)
 * 5) An empty right-side, x <- , expresses that x is empty
 * 6) Sequences of variables or constants use a regex-like convention for
 *    multiplicity
 *   a) x*  -- 0 or more variables
 *   b) D+  -- 1 or more concrete fields
 *   c) y++ -- 2 or more variables
 * 7) Rules that infer something about partitioning of a sequence of variables
 *    xQ, where Q inhabits {*,+,++,...} will be written (x <- ..)Q
 * 8) Named individuals or sequences are expected to be coherent, distinct and
 *    disjoint over an entire inference rule:
 *   a) x* y* -- two disjoint sequences of 0 or more variables
 *   b) x x   -- the same variable twice
 *   c) f <- x+ y*, f <- x+ z* ...
 *       -- three disjoint sequences of variables
 *
 * ---------------
 * Inference Rules
 * ---------------
 *
 * This section describes the inference rules used by the solver to gain new
 * information. Unless otherwise noted, the rules are not destructive, so
 * if the first half of a rule applies to the constraint environment, the
 * second half will be added, but the constraints in the first half will
 * not be removed from the environment.
 *
 * Inference rules will be written vertically, with a vertical list of initial
 * constraints, followed by a bar, followed by the vertical list of output
 * constraints.
 *
 *  Self-substitution
 *
 *   If a variable is partitioned into itself and additional variables,
 *   those additional variables can only be empty.
 *
 *    a <- a b*
 *    ---------
 *      b <-
 *
 *
 *  Empty partition
 *
 *   If a variable is empty, and it is partitioned into one or more variables,
 *   those variables can only be empty.
 *
 *    a <-
 *    a <- x+
 *    -------
 *    (x <-)+
 *
 *
 *  De-duplication
 *
 *   If a partition includes a given variable twice, that variable can only be
 *   empty.
 *
 *    a <- C* x* b b
 *    --------------
 *         b <-
 *
 *
 *  Split concrete
 *
 *   If a variable is partitioned into some fields and more than one variable,
 *   it is useful to name that sequence of variables.
 *
 *    a <- C+ x++
 *    -----------
 *     u <- x++    (u fresh)
 *     a <- C+ u
 *
 *
 *  Cancellation
 *
 *   If we have two partitions of a variable, and the intersection of the
 *   partitions leaves a lone variable as the remainder of one, then we
 *   can infer that that single variable must be partitioned into the
 *   remainder of the other.
 *
 *    a <- C* x* z
 *    a <- C* x* D* d*
 *    ----------------
 *       z <- D* d*
 *
 *
 *  Resolution
 *
 *   If we have two partitions of a variable, each containing a lone variable
 *   on the right, we may infer that the left variable contains all the fields
 *   from both rules, and that each of the lone right variables contain the
 *   fields missing from their rule.
 *
 *     a <- C* D* x
 *     a <- y  D* E*
 *    ---------------
 *    a <- C* D* E* z  (z fresh)
 *       x <- C* z
 *       y <- E* z
 *
 *
 *  Substitution
 *
 *   We may substitute a variable with its partition.
 *
 *      a <- D* b x*
 *       b <- F* y*
 *    ----------------
 *    a <- D* F* x* y*
 *
 *
 *  Common partition
 *
 *   If two variables are partitioned identically, we may unify them.
 *
 *    a <- A* x*
 *    b <- A* x*
 *    ----------
 *      a <- b
 *
 *
 *  Common subexpression
 *
 *   It is useful to give names to the largest common variable subexpression
 *   between two rules.
 *
 *    a <- C* x++ y*
 *    b <- D* x++ z*
 *    --------------
 *       w <- x++     (w fresh)
 *     a <- C* w y*
 *     b <- D* w z*
 *
 *
 *  Disjunction
 *
 *   If we know that a set of variables lack a set of fields and variables,
 *   we may be able to infer that another variable set _has_ the respective,
 *   fields and variables.
 *
 *    r1 <- A* a* C* c* z+       S* s*
 *    r2 <- A* a* C* c*    R* r* T* t*
 *    r2 <- A* a*    u+ z+ R* r* U*
 *    C* c* non-empty
 *    --------------------------------------
 *    u+ <- C* c* v (v fresh)
 *
 *  Generalized cancellation !!
 *
 *   We may apply cancellation in a case without a lone variable so long as
 *   we give a name to the multiple variables in question.
 *
 *    a <- C* e* x++
 *    a <- C* e* D* d*
 *    ----------------
 *        u <- x++      (u fresh)
 *       u <- D* d*
 *
 *
 * ----------------
 * Error conditions
 * ----------------
 *
 * Certain constraints or combinations thereof are verifiably
 * unsatisfiable.
 *
 *  Duplicated field
 *
 *   A field cannot appear twice in a row.
 *
 *    a <- C* x* D D
 *    --------------
 *    a inconsistent
 *
 *  Incompatible fields
 *
 *   If we have a concrete substitution for a variable, it must
 *   contain all the fields that other rules say the variable contains.
 *
 *         a <- C* D*
 *         a <- D* E+ x*
 *    ------------------------
 *    C* doesn't subsume E+ x*
 *
 *  Infinite fields
 *
 *   A variable cannot both contain and be disjoint from a field.
 *
 *    a <- C+ a x*
 *    ------------
 *
 * ---------
 * Miscelany
 * ---------
 *
 * Applying the above rules only to learn things, never throwing anything
 * away, and the necessity of comparing every partition against every other
 * for each pass, one would probably expect an algorithm using the rules
 * above to not perform very well. So, a strategy for discarding partitions
 * when possible is desirable. The following are some ideas:
 *
 * 1) Whenever we have a concrete substitution for a variable, we would like
 *    to eliminate partitions involving it. However, we have to take care
 *    not to lose any information. There are two safeguards that we believe
 *    are sufficient:
 *
 *     a) along with the concrete substitution a <- C*, perform all other
 *        substitutions for left-a rules
 *     b) ensure that at least one substitution occurs (i.e. that a is on
 *        the right of at least one rule)
 *
 *    these together ensure that, for instance, in the case of a <- b c
 *    the information that b is disjoint from c is not lost, because we've
 *    substituted 'b c' in for 'a' in some other rule.
 *
 *    In addition, we must inform the standard unifier that we have a
 *    concrete substitution for the variable. This will ensure that rules
 *    about it are never needed later, because the variable will have been
 *    replaced with a concrete expression.
 *
 *    Given these safeguards, we should be able to eliminate all rules
 *    mentioning the concretized variable from the solver state.
 *
 * 2) At some point, constraint solving must end, and we must collapse the
 *    constraint environment into something that can be preprended to a
 *    type. At this point, we can trim the constraint environment by
 *    searching for a small set of constraints that imply the others.
 */

import scala.util._

import scalaz._
import Scalaz._
import Lens._
import Foldable._
import Tags._

import com.clarifi.reporting.ermine.Document._
import com.clarifi.reporting.util._
import StreamTUtils._

import Type._

object Constraints {
  import Subst._
  // a handy pattern
  object Single {
    def unapply[A](s: Set[A]): Option[A] =
      if(s.size == 1)
        Some(s head)
      else
        None
  }

  /* Invariant: the set of partitioning constraints will always contain
   * sets on the right-hand side. Duplicates will be detected upon rule
   * formation, and the relevant inference or error rule applied
   * immediately.
   *
   * Further, the names of constants in the set of parts should be
   * unique.
   */

  type Fields = Set[Name]

  def displayRHS: RHS => String = {
    case RHS(a, c) =>
      "(|" + c.mkString(", ") + (if(a isEmpty) "" else " ..") + "|)"
  }

  def displayFields(s: Set[String]) = "(|" + s.mkString(", ") + "|)"

  // LongModuleName.foo, LongModuleName.bar gets displayed as
  // LongModuleName.{foo, bar}
  def displayFactoredRow(fs: Fields, indent: String): String = {
    def factorQualifier(p: (Option[String],List[Name])): String =
      p._1.map(_ + ".").getOrElse("") +
      (if (p._2.length == 1) p._2.head.string
       else {
         val newline = if (p._2.length < 4) "" else "\n  " + indent
         "{ " + newline + p._2.map(_.string).sorted.mkString(", "+newline) + " }"
       })
    val factored = fs.toList.groupBy(_.qualifier).toList.
                   sortBy(_._1).map(factorQualifier)
    if (fs.size < 4) indent + factored.mkString(", ")
    else             indent + factored.mkString(",\n" + indent)
  }

  // @throws SubstException
  def ensureSuperset(loc: Loc, sub: Fields, sup: Fields)(implicit tml: Located) =
    if (!(sub subsetOf sup))
      die {
        "Row types failed to unify: " :/:
        "R1 = " :/: displayFactoredRow(sub, "  ") :/:
        "R2 = " :/: displayFactoredRow(sup, "  ") :/:
        loc.report("R1") :/:
        tml.report("R2")
      }

  private def predOr[A](p1: A => Boolean, p2: A => Boolean)(x: A): Boolean = p1(x) || p2(x)

  // The right hand side of a partition constraint
  case class RHS(abstr: Set[TypeVar] = Set(), concr: Fields = Set()) {
    def isConcrete = abstr isEmpty

    def isEmpty = (abstr isEmpty) && (concr isEmpty)

    def -(v: TypeVar): RHS = RHS(abstr - v, concr)

    def contains(v: TypeVar): Boolean = abstr contains v

    // @throws SubstException
    def merge(rhs: RHS)(implicit tml: Located): (RHS, Set[TypeVar]) = rhs match {
      case RHS(abs, con) => {
        val aint = abstr & abs
        val cint = concr & con

        if (cint.isEmpty) (RHS((abstr ++ abs) -- aint, concr ++ con), aint)
        else tml.die("Fields appear twice in row: " + cint)
      }
    }

    // @throws SubstException
    def substitute(v: TypeVar, rhs: RHS)(implicit tml: Located): (RHS, Set[TypeVar]) =
      if(abstr contains v) (this - v) merge rhs
      else (this, Set())

    def vars: Vars[Kind] = Vars(abstr)

    def toTypes(loc: Loc): List[Type] = {
      val vs = abstr.toList.map(VarT(_))
      if(concr.isEmpty)
        vs
      else
        ConcreteRho(loc, concr) :: vs
    }
  }

  // RHS views
  object RHSEmpty {
    def unapply(rhs: RHS): Boolean = rhs isEmpty
    def apply(): RHS = RHS()
  }
  object RHSAbstr {
    def unapply(rhs: RHS): Option[Set[TypeVar]] = rhs match {
      case RHS(abs, con) if con isEmpty => some(abs)
      case _                            => none
    }
    def apply(abstr: Set[TypeVar]): RHS = RHS(abstr, Set())
  }
  object RHSConcr {
    def unapply(rhs: RHS): Option[Fields] = rhs match {
      case RHS(abs, con) if abs isEmpty => some(con)
      case _                            => none
    }
    def apply(concr: Fields): RHS = RHS(Set(), concr)
  }

  object RHS {
    def build(ts: List[Type])(implicit tml: Located): (RHS, List[TypeVar]) = {
      val (abs, con, e) = ts.foldLeft((Set[TypeVar](), Set[Name](), Set[TypeVar]())) {
        case ((a, c, e), ConcreteRho(l, s)) =>
          val i = c.intersect(s)
          if(i.nonEmpty)
            tml.die("Fields appear twice in row: " + i.mkString(","))
          else (a, c ++ s, e)
        case ((a, c, e), VarT(v)) =>
          if(a.contains(v) || e.contains(v))
            (a - v, c, e + v)
          else
            (a + v, c, e)
        case ((a, c, e), Con(_, n, _, _)) => (a, c + n, e)
        case (_, t) => tml.die(t.report("panic: Malformed constraint, RHS" :+: text(t.toString)))
      }
      (RHS(abs, con), e.toList)
    }
  }

  type IntMap[TypeVar] = Map[Int, TypeVar]

  object Q {
    def substSet(u: TypeVar, v: TypeVar, s: Set[TypeVar]) = if(s contains u) s - u + v else s

    // Invariant: sort is a valid topological sorting of nodes given edges
    case class TypeVarGraph(nodes: Set[TypeVar], edges: Map[TypeVar, Set[TypeVar]], sort: Map[TypeVar, Int]) {
      def +(p: (TypeVar, Set[TypeVar])): (TypeVarGraph, Boolean) = p match {
        case (u, vs) => {
          val newNodes = nodes ++ vs + u
          val newEdges = edges.get(u) match {
            case None    => edges + (u -> vs)
            case Some(s) => edges + (u -> (s ++ vs))
          }

          def indexMap(s: Stream[TypeVar]): Map[TypeVar, Int] =
            s.zip(Stream.from(0)).toMap

          def edgeFun(v: TypeVar): Stream[TypeVar] = newEdges.get(v) cata (_.toStream, Stream[TypeVar]())

          if(sort.contains(u) && vs.forall(v => sort.contains(v) && (sort(v) < sort(u))))
            (TypeVarGraph(newNodes, newEdges, sort), false)
          else
            (TypeVarGraph(newNodes, newEdges,
              indexMap(reverseTopSort(newNodes.toStream)(edgeFun))), true)
        }
      }

      def + : Partition => (TypeVarGraph, Boolean) = {
        case Partition(u, RHS(vs, _), _) => this + (u -> vs)
      }

      def rename(u: TypeVar, v: TypeVar): TypeVarGraph = {
        val nnodes = substSet(u, v, nodes)
        val nedges = edges map { case (k, s) => (if(k == u) v else k, substSet(u, v, s)) }
        val nsort = if(sort contains u) sort - u + (v -> sort(u)) else sort
        TypeVarGraph(nnodes, nedges, nsort)
      }
    }

    object TypeVarGraph {
      def empty: TypeVarGraph = TypeVarGraph(Set(), Map(), Map())
    }

    // (empty(priority, (right hash, left hash)), size)
    type PSQK = (Option[(Int, (Int, Int))], Int)
    type PSQI = FingerTree[PSQK, Partition]

    def pr(graph: TypeVarGraph): Reducer[Partition, PSQK] = {
      def mon: Monoid[PSQK] = new Monoid[PSQK] {
        val zero = (none, 0)
        def append(s1: PSQK, s2: => PSQK): PSQK = {
          val sz = s1._2 + s2._2

          s1._1 match {
            case None => (s2._1, sz)
            case Some((prl, tpl)) => s2._1 match {
              case None => (s1._1, sz)
              case Some((prr, tpr)) => (some((prl min prr, tpr)), sz)
            }
          }
        }
      }
      UnitReducer[Partition, PSQK] { case Partition(lhs, rhs, _) =>
        (some(graph.sort(lhs), (rhs.hashCode, lhs.hashCode)), 1) } {mon}
    }

    def heapify(q: PSQI, graph: TypeVarGraph): PSQI = {
      implicit def r = pr(graph)

      // I think this should replace the reducer
      q.foldRight(FingerTree.empty)(_ +: _)
    }

    def part[K: Order](q: PSQI, f: PSQK => K, k: K): (PSQI, PSQI, PSQI) = {
      val (less, geqs) = q.split(f(_) gte k)
      val (equal, greater) = geqs.split(f(_) gt k)

      (less, equal, greater)
    }

    def rhsLookup(rhs: RHS, q: PSQI, exe: Boolean): Option[TypeVar] = if(exe) rhs match {
      case RHSEmpty()          => None // Don't common-out empty partitions
      case RHSAbstr(Single(_)) => None // nor unification partitions
      case _ => q.foldRight(none[TypeVar])((p: Partition, r) => if(p._2 == rhs) some(p._1) else r)
    } else None

    // Inserts a partition into the queue, returning a new queue and an updated
    // graph. The boolean determines whether the rule should be processed for
    // common right-hand sides.
    def insert(p: Partition, q: PSQI, graph: TypeVarGraph, process: Boolean): (PSQI, TypeVarGraph) =
      if(p.isSelfUnification) (q, graph)
      else {
        val (hcr, hcl) = p match {
          case Partition(lhs, rhs, _) => (rhs.hashCode, lhs.hashCode)
        }

        val (rlt, req, rgt) = part(q, (_._1.map(_._2._1)), some(hcr))

        val (llt, leq, lgt) = part(req, (_._1.map(_._2._2)), some(hcl))

        def sandwich: (PSQI, TypeVarGraph) = {
          val (newGraph, reheap) = graph + p

          def hp(nq: PSQI) = if(reheap) heapify(nq, newGraph) else nq

          val left  = hp(rlt <++> llt)
          val right = hp(leq <++> lgt <++> rgt)

          (left <++> (p +: right), newGraph)
        }

        if(leq any (p == _)) (q, graph)
        else rhsLookup(p._2, req, process) match {
          case Some(v) =>
            insert(Partition(v, RHSAbstr(Set(p._1)), CommonPartition), q, graph, false)
          case None    => sandwich
        }
      }

    def pop(q: PSQI, graph: TypeVarGraph): Option[(Partition, PSQI)] = {
      val priority = q.measure._1.map(_._1)

      val (lhs, rhs) = q.split(k => k._1.map(_._1) == priority)

      rhs.viewl.fold(none, (p, rest) => some((p, lhs <++> rest)))
    }

    class PQueue(val q: PSQI, graph: TypeVarGraph) extends Traversable[Partition] {

      def foreach[U](f: Partition => U): Unit = q.foreach(x => { f(x) ; () })

      // Inserts a partition into the queue without any processing
      def +(p: Partition): PQueue = {
        val (nq, ng) = insert(p, q, graph, false)

        new PQueue(nq, ng)
      }

      // Iterated +
      def ++(ps: Traversable[Partition]): PQueue = ps.foldLeft(this)(_ + _)

      // Iterated +
      def ++(ps: PQueue): PQueue = ps.foldLeft(this)(_ + _)

      // Inserts a partition into the queue, checking for common right-hand
      // sides and making a unification instead if applicable.
      def +!(p: Partition): PQueue = {
        val (nq, ng) = insert(p, q, graph, true)

        new PQueue(nq, ng)
      }

      // Iterated +!
      def ++!(ps: Traversable[Partition]): PQueue = ps.foldLeft(this)(_ +! _)

      // Iterated +!
      def ++!(ps: PQueue): PQueue = ps.foldLeft(this)(_ +! _)

      def dequeue: Option[(Partition, PQueue)] =
        pop(q, graph) map (_ :-> (new PQueue(_, graph)))

      override def filter(pred: Partition => Boolean): PQueue = {
        implicit def r = pr(graph)
        val nq = q.foldRight(FingerTree.empty)((e,r) => if(pred(e)) e +: r else r)

        new PQueue(nq, graph)
      }

      override def partition(pred: Partition => Boolean): (Set[Partition], PQueue) = {
        implicit def r = pr(graph)
        val (ps, nq) = q.foldRight((Set[Partition](),FingerTree.empty)){
          case (e, (l, r)) => if(pred(e)) (l + e, r) else (l, e +: r)
        }

        (ps, new PQueue(nq, graph))
      }

      override def isEmpty: Boolean = q.isEmpty

      override def size: Int = q.measure._2

//      def toSet: Set[Partition] = q.foldLeft(Set[Partition]())(_ + _)

      def foldRight[R](z: => R)(f: (Partition, => R) => R): R = q.foldRight(z)(f)

      override def foldLeft[R](z: R)(f: (R, Partition) => R): R = q.foldLeft(z)(f)

      def foldM[M[_]:Monad,R](z: R)(f: (R, Partition) => M[R]): M[R] =
        q.foldRight((z: R) => z.pure[M])((p, k) => (z: R) => f(z, p) >>= k).apply(z)

      def findRHS(rhs: RHS): Option[TypeVar] = {
        val i = rhs.hashCode

        def onRHS(p: Int => Boolean): PSQK => Boolean = {
          case (None             , _) => true
          case (Some((_, (r, _))), _) => p(r)
        }

        val (_, geqs) = q.split(onRHS(i <= _))
        val (eqs, _) = geqs.split(onRHS(i < _))

        eqs.foldRight[Option[TypeVar]](none) {
          case (Partition(lhs, rhs2, _), r) =>
            if(rhs == rhs2) some(lhs)
            else            r
        }
      }

      override def forall(p: Partition => Boolean): Boolean = q all p
      override def exists(p: Partition => Boolean): Boolean = q any p

      def contains(p: Partition): Boolean = p match {
        case Partition(lhs, rhs, _) =>
          part(q, (_._1.map(_._2)), some((rhs.hashCode, lhs.hashCode)))._2 any (p == _)
      }

      override def toString: String = foldRight("")((p, s) => "\n  " + p.toString + s)

      def expand(implicit hm: SubstEnv, su: Supply, tml: Located): PQueue = incorporateAll(this, PQueue())

      def vars: Vars[Kind] = foldRight(Vars() : Vars[Kind])((p, r) => r ++ Vars(p._1) ++ p._2.vars)

      def toType(loc: Loc, quantified: Set[TypeVar]): Type = {
        val toQuant = (vars -- quantified).toList
        val ps = foldRight(List() : List[Type])((p, r) => Part(loc, VarT(p._1), p._2.toTypes(loc)) :: r)

        ps match {
          case List(p) if toQuant.isEmpty => p
          case _ => Exists.mk(loc, toQuant, ps)
        }
      }
    }

    object PQueue {
      private def empty: PQueue = {
        implicit def r = pr(TypeVarGraph.empty)
        new PQueue(FingerTree.empty, TypeVarGraph.empty)
      }

      def apply(ps: Partition*) = empty ++ ps
      def apply(ps: Traversable[Partition]) = empty ++ ps

      // @throws SubstException
      def build(v: TypeVar, t:Type)(implicit tml: Located): PQueue = t match {
        case VarT(v) => PQueue(Partition(v, RHSAbstr(Set(v))))
        case ConcreteRho(_, s) => PQueue(Partition(v, RHSConcr(s)))
        case _ => tml.die(t.report("Non-row in expected row position", t.toString))
      }

      // @throws SubstException
      def build(t: Type)(implicit su: Supply, tml: Located): (PQueue,List[TypeVar]) = {
        def aux(t: Type): (List[Partition], List[TypeVar]) = t match {
          case e : Exists =>
            val (us, ts) = unbindExists(Ambiguous(Free), e)
            val (pss, vss) = ts.map(aux _).unzip
            (pss.flatten, vss.flatten)
          case Part(loc, VarT(v), rhsz) =>
            val (rhs, es) = RHS.build(rhsz)
            (Partition(v, rhs) :: es.map(u => Partition(u, RHSEmpty())), List())
          case Part(loc, lhs, rhs) => // lhs is not a variable
            val v = fresh(loc, none, Ambiguous(Free), Rho(loc.inferred))
            val (rhs1, es1) = RHS.build(rhs)
            val (rhs2, es2) = RHS.build(List(lhs))
            (Partition(v, rhs1) :: Partition(v, rhs2) :: (es1 ++ es2).map(u => Partition(u, RHSEmpty())), List())
          case _ =>
            (List(),List())
            // t.die("panic: malformed constraint:" :+: text(t.toString))
        }
        val (ps, vs) = aux(t.nf)
        (PQueue(ps), vs)
      }
    }
  }

  import Q.PQueue

  // An enumeration for inference rules, used to track which rule
  // introduced a particular partition.
  sealed trait Inference
  case object Resolution          extends Inference
  case object Cancellation        extends Inference
  case object SelfSubstitution    extends Inference
  case object Substitution        extends Inference
  case object PartitionEmpty      extends Inference
  case object SplitConcrete       extends Inference
  case object CommonPartition     extends Inference
  case object DeDuplication       extends Inference
  case object CommonSubexpression extends Inference
  case object Disjunction         extends Inference

  case class Partition(_1: TypeVar, _2: RHS, inf: Option[Inference]) {
    def tup: (TypeVar, RHS) = (_1, _2)

    override def toString: String = {
      def pvar: TypeVar => String = {
        case V(_,i,_,ty,_) => '^' + ty.toString.toLowerCase + i.toString
      }
      def prhs: RHS => String = {
        case RHS(abs,con) => ( abs.map(pvar).mkString(" ")
                             , con.mkString(" ")).toString
      }
      val pinf = inf.cata(x => x.toString + ": ", "")

      pinf + pvar(_1) + " <- " + prhs(_2)
    }

    override def equals(v: Any) = v match {
      case Partition(u, r, _) => _1 == u && _2 == r
      case _                  => false
    }

    override def hashCode: Int = (_1, _2).hashCode

    def isSelfUnification: Boolean = _2 match {
      case RHSAbstr(Single(u)) => u == _1
      case _                   => false
    }
  }

  object Partition {
    def apply(v: TypeVar, rhs: RHS, inf: Inference): Partition = Partition(v, rhs, some(inf))
    def apply(v: TypeVar, rhs: RHS): Partition = Partition(v, rhs, none)
    def apply(p: (TypeVar, RHS)): Partition = Partition(p._1, p._2, none)
  }

  def ruleInvolves(u: TypeVar): Partition => Boolean = {
    case Partition(v, rhs, _) => u == v || rhs.contains(u) }

  def trim(ps: Set[Partition], cs: PQueue): Set[Partition] =
    ps.filter(p => !(cs contains p))

  def findRHS(ps: PQueue, cs: PQueue, s: Set[Partition])(rhs: RHS): Option[TypeVar] =
    (First(cs.findRHS(rhs)) |+| First(ps.findRHS(rhs)) |+| First(s.find(_._2 == rhs).map(_._1)))

  /* Merges a well-formed constraint into cs.
   *
   * We also take care of the following rules here:
   *
   *  Common partition
   *
   *    a <- A* x*
   *    b <- A* x*
   *    ----------
   *      a <- b
   */

  def combine(q1: PQueue, q2: PQueue)(implicit hm: SubstEnv, su: Supply, tml: Located): PQueue =
    if(q1.size < q2.size)
      incorporateAll(q2, q1)
    else
      incorporateAll(q1, q2)

  def incorporateAll(incm: PQueue, proc: PQueue)(implicit hm: SubstEnv, su: Supply, tml: Located): PQueue = incm.dequeue match {
      case None => proc
      case Some((r@Partition(v, rhs, _), rest)) =>
//        System.err.println(r)
//        println("incoming")
//        println(rest.toString)
//        println("processed")
//        println(proc.toString)
//        println("--------------------")
        val (nincm, nproc) = proc findRHS(rhs) match {
          case Some(u) => unify(v, u, rest, proc) // common partition
          case None    => rhs match {
            case RHSEmpty()          => makeEmpty(v, rest, proc)
            case RHSConcr(concr)     => makeConcrete(v, concr, rest, proc)
            case RHSAbstr(Single(u)) => unify(u, v, rest, proc)
            case RHS(abstr,concr)    => (rest ++! trim(learnPartitions(v, rhs, rest, proc), proc), proc + r)
          }
        }
        incorporateAll(nincm, nproc)
    }

  /*
   *  Self substitution
   *
   *    a <- a b*
   *    ----------
   *     (b <-)*
   *
   *    a <- C+ a b*
   *    ------------
   *       error
   */
  // @throws SubstException
  def selfSubstitution(v: TypeVar, abstr: Set[TypeVar], concr: Fields)(implicit tml: Located): Set[Partition] =
    if(concr isEmpty) (abstr - v).map(u => Partition(u, RHS(), SelfSubstitution))
    else tml.die("Infinite row partition for '" + v + "'")

  /* The actual calculation of the split concrete rule
   *
   *  Split concrete
   *
   *    a <- C+ x++
   *    -----------
   *     u <- x++    (u fresh)
   *     a <- C+ u
   */
  def splitConcrete(v: TypeVar, abstr: Set[TypeVar], concr: Fields, rhss: RHS => Option[TypeVar])(implicit su: Supply): Set[Partition] =
    if(concr.isEmpty || abstr.size < 2) Set()
    else // split concrete
      rhss(RHSAbstr(abstr)) match {
        case Some(u) => Set(Partition(v, RHS(Set(u), concr), SplitConcrete))
        case None    =>
          val u = fresh(Loc.builtin, none, Ambiguous(Free), Rho(Loc.builtin))
          Set( Partition(u, RHSAbstr(abstr), SplitConcrete)
             , Partition(v, RHS(Set(u), concr), SplitConcrete))
      }

  /* When the above special case rules haven't fired, we need to collect
   * up new rules based on the rule we're about to add, and the other
   * rules that have been incorporated already.
   */
  // @throws SubstException
  def learnPartitions(v: TypeVar, rhs1: RHS, incm: PQueue, proc: PQueue)(implicit su: Supply, tml: Located): Set[Partition] =
    if(rhs1.abstr contains v) selfSubstitution(v, rhs1.abstr, rhs1.concr)
    else proc.foldLeft[Set[Partition]](
           splitConcrete(v, rhs1.abstr, rhs1.concr, findRHS(incm, proc, Set()))
         ){
           case (s, Partition(u, rhs2, _)) =>
             if(u == v) {
               val rps = resolution(v, rhs1, rhs2)
               val cps = cancellation(v, rhs1, rhs2)
//               val dps = proc.toList.flatMap {
//                 case Partition(w, rhs3, _) if w != v => disjunction(rhs3, rhs1, rhs2) ++ disjunction(rhs3, rhs2, rhs1)
//                 case _                               => Set[Partition]()
//               }
               (s ++ rps ++ cps) // ++ dps)
             }
             else {
               val csps = commonSubexpression(v, rhs1, u, rhs2, findRHS(incm, proc, s))
               val sps  = substitution(v, rhs1, u, rhs2)
//               val dps  = proc.toList.flatMap {
//                 case Partition(w, rhs3, _) =>
//                   if(w == u && rhs2 != rhs3)
//                     disjunction(rhs1, rhs2, rhs3) ++ disjunction(rhs1, rhs3, rhs2)
//                   else if(w == v && rhs1 != rhs3)
//                     disjunction(rhs2, rhs1, rhs3) ++ disjunction(rhs2, rhs3, rhs1)
//                   else
//                     Set[Partition]()
//               }
               (s ++ csps ++ sps) // ++ dps)
             }
         }

  def simpleSubst(v: TypeVar, u: TypeVar, w: TypeVar)(r : Partition): PQueue = {
    def f(z: TypeVar) = if(z == v || z == u) w else z
    r match {
      case Partition(z, RHS(abs,con), inf) => {
        def g(b: Boolean): Int = if(b) 1 else 0

        val multi = g(abs contains v) + g(abs contains u)
                  + g(abs.contains(w) && (w != v) && (w != u))

        if(multi > 1)
          PQueue(Partition(f(z), RHS(abs - v - u - w, con), inf),
                 Partition(w, RHSEmpty(), DeDuplication))
        else
          PQueue(Partition(f(z), RHS(abs map f, con), inf))
      }
    }
  }

  /* This handles unification of two variables, once the rules have
   * determined that such a thing should happen. This is another
   * destructive procedure, as all references to one should be
   * replaced with the other in our constraints.
   */
  // @throws SubstException
  def unify(v: TypeVar, u: TypeVar, incm: PQueue, proc: PQueue)(implicit hm: SubstEnv): (PQueue, PQueue) =
    if (v == u) (incm, proc) else instantiate(v, u, incm, proc)

  def replace(v: TypeVar, u: TypeVar, p: Partition): PQueue = p match {
    case Partition(z, RHS(abs, con), inf) =>
      def f(w: TypeVar) = if(w == v) u else w
      val partp = Partition(f(z), RHS(abs.map(f _), con), inf)
      if(abs.contains(v) && abs.contains(u))
        PQueue(partp, Partition(u, RHSEmpty(), DeDuplication))
      else PQueue(partp)
  }

  // @throws SubstException
  def instantiate(v: TypeVar, u: TypeVar, incm: PQueue, proc: PQueue)(implicit hm: SubstEnv): (PQueue, PQueue) = {
    val (pps, nproc) = proc partition ruleInvolves(v)
    val (qps, nincm) = incm partition ruleInvolves(v)
    val nps = pps ++ qps
    instantiateType(v, VarT(u))
    (nps.foldLeft(nincm)((nq, p) => nq ++! replace(v,u,p)), nproc)
  }

  /* Empty is a somewhat special concrete substitution. It's probably best to
   * handle it separately.
   *
   * This handles the partition empty rule:
   *
   *   a <-
   *   a <- x+
   *  ---------
   *   (x <-)+
   *
   * as well as a special case of one of the incompatibility rules: a row
   * cannot both be empty and have fields.
   *
   * This 'destructively' modifies both cs and rs to incorporate the fact that
   * v has been made empty, collecting up additional rules that are a
   * consequence of v being made empty.
   *
   * This also informs the normal unifier that v is the empty row.
   */
  // @throws SubstException
  def makeEmpty(v: TypeVar, incm: PQueue, proc: PQueue)(implicit hm: SubstEnv, tml: Located): (PQueue, PQueue) = {
    def aux(s: Set[Partition], rhs: RHS): Set[Partition] = rhs match {
      case RHSEmpty()      => s
      case RHSAbstr(abstr) => s ++ abstr.map(v => Partition(v, RHSEmpty(), PartitionEmpty))
      case _               => tml.die("Incompatible instantiations of '" + v + "'")
    }

    val (pps, procd) = proc partition ruleInvolves(v)
    val (qps, incmg) = incm partition ruleInvolves(v)

    val nps = (qps ++ pps).foldLeft(Set[Partition]()){
      case (s, Partition(u, rhs, inf)) =>
          if(u == v) aux(s, rhs)
          else s + Partition(u, rhs - v, inf)
    }

    if (v.ty == Skolem) tml.die(v.report("Cannot unify skolem variable with empty relation", v.toString))

    instantiateType(v, ConcreteRho(Loc.builtin, Set()))
    (incmg ++! trim(nps,procd), procd)
  }

  /* Given a substitution, a partition set, and a set of incoming rules,
   * computes all the rules that need to be added due to the substitution.
   */

  // @throws SubstException
  def subPartitions(v: TypeVar, sub: RHS, proc: PQueue, incm: PQueue)(implicit tml: Located): Set[Partition] = {
    def reduce(s: Set[Partition], r: Partition) = r match {
      case Partition(u, rhs, old) if rhs contains v =>
        val (nrhs, es) = rhs substitute (v, sub)
        (s ++ es.map(w => Partition(w, RHS(), DeDuplication)) + Partition(u, nrhs, old))
      case Partition(u, rhs, _) => s
    }
    incm.filter(_._1 != v).foldLeft(proc.foldLeft(Set[Partition]())(reduce))(reduce)
  }

  /* Handles the case where we have a concrete substitution for a variable.
   */
  def makeConcrete(v: TypeVar,
                   fs: Fields,
                   incm: PQueue,
                   proc: PQueue)(implicit hm: SubstEnv, tml: Located): (PQueue,PQueue) = {
    val rhss = (proc.toSet.filter(p => p._1 == v).map(_._2)
             ++ incm.toSet.filter(p => p._1 == v).map(_._2))
      // Check superset compatibility for the concrete instantiation
    rhss.foreach {
      case RHS(_, concr) => ensureSuperset(v.loc, concr, fs)
    }
    val can = rhss.foldLeft(Set[Partition]()){
      case (s, rhs) => s ++ cancellation(v, RHSConcr(fs), rhs)
    }
    val (nincm, nproc) = destructiveSub(v, RHSConcr(fs), incm, proc)
    (nincm ++! can, nproc + Partition(v, RHSConcr(fs)))
  }

  /* Given a rule, a set of incoming rules, and a partition set, computes the
   * partition set and new set of incoming rules appropriate for destructively
   * substituting rhs for v.
   */
  // @throws SubstException
  def destructiveSub(v: TypeVar,
                     rhs: RHS,
                     incm: PQueue,
                     proc: PQueue)(implicit hm: SubstEnv, tml: Located): (PQueue, PQueue) = {
    val (pps, procd) = proc partition(p => p._1 == v)
    val (qps, incmg) = incm partition(p => p._1 == v)
    val keep = !((pps union qps).isEmpty)
    val srs = (pps ++ qps).map(_._2).foldLeft(subPartitions(v, rhs, procd, incmg)){
      case (s, rhs) => s ++ subPartitions(v, rhs, procd, incmg)
    }
    val p : Partition => Boolean = { case Partition(u, rhs, _) => u != v && !rhs.contains(v) }
    val nproc = if((srs isEmpty) && keep) proc else procd filter p
    val nincm = if((srs isEmpty) && keep) incm else incmg filter p
    (nincm ++! trim(srs,nproc), nproc)
  }

  /*
   * Rules
   */

  /* Cancellation
   *
   *  a <- C* x* z
   *  a <- C* x* D* y*
   *  ----------------
   *     z <- D* y*
   */
  def cancellation(v: TypeVar, rhs1: RHS, rhs2: RHS): Set[Partition] = (rhs1, rhs2) match {
    case (RHS(abs1, con1), RHS(abs2, con2)) => {
      val absInt = abs1 & abs2
      val conInt = con1 & con2

      // v <- C* e* F* x*
      // v <- C* e* G* y*
      val xs = abs1 -- absInt
      val ys = abs2 -- absInt
      val fs = con1 -- conInt
      val gs = con2 -- conInt

      if(fs.isEmpty && xs.size == 1)
        Set(Partition(xs.head, RHS(ys, gs), Cancellation))
      else if (gs.isEmpty && ys.size == 1)
        Set(Partition(ys.head, RHS(xs, fs), Cancellation))
      else
        Set()
    }
  }

  /* Resolution
   *
   *    a <- C+ D* x
   *    a <- y  D* E+
   *   ---------------
   *   a <- C+ D* E+ z  (z fresh)
   *      x <- E+ z
   *      y <- C+ z
   */
  def resolution(v: TypeVar, rhs1: RHS, rhs2: RHS)(implicit su: Supply): Set[Partition] = (rhs1, rhs2) match {
    case (RHS(Single(x), concr1), RHS(Single(y), concr2)) =>
      val z = fresh(Loc.builtin, none, Ambiguous(Free), Rho(Loc.builtin))
      val int = concr1 & concr2
      val tops = concr1 -- int
      val bots = concr2 -- int
      if(tops.isEmpty || bots.isEmpty) Set() // Such cases are handled by cancellation
      else Set(Partition(v, RHS(Set(z), concr1 ++ concr2), Resolution),
               Partition(x, RHS(Set(z), bots), Resolution),
               Partition(y, RHS(Set(z), tops), Resolution))
    case _ => Set()
  }

  // @throws SubstException
  def subBody(v: TypeVar, rhs1: RHS, u: TypeVar, rhs2: RHS)(implicit tml: Located): Set[Partition] =
    if(rhs2 contains v) {
      val (nrhs, es) = rhs2 substitute (v, rhs1)
      (es.map(v => Partition(v, RHS(), DeDuplication)) + Partition(u, nrhs, Substitution))
    } else Set()

  /* Substitution
   *
   *  a <- D* b x*
   *  b <- E* y*
   *  ------------
   *  a <- D* E* x* y*
   */
  // @throws SubstException
  def substitution(v: TypeVar, rhs1: RHS, u: TypeVar, rhs2: RHS)(implicit tml: Located): Set[Partition] =
    subBody(v, rhs1, u, rhs2) ++ subBody(u, rhs2, v, rhs1)

  /* Common subexpression
   *
   *  a <- C* E* x++ y*
   *  b <- D* E* x++ z*
   *  -----------------
   *   w <- x++          (w fresh)
   *   a <- C* E* w y*
   *   b <- D* E* w z*
   */

  def commonSubexpression(v: TypeVar, rhs1: RHS, u: TypeVar, rhs2: RHS, rhss: RHS => Option[TypeVar])(implicit su: Supply): Set[Partition] =
    (rhs1, rhs2) match {
      case (RHS(abstr1, concr1), RHS(abstr2, concr2)) =>
        val int = abstr1 & abstr2
        val rhsCommon = RHSAbstr(int)
        if(int.size < 2) Set()
        else rhss(rhsCommon) match {
          case Some(z) =>
            Set(Partition(v, RHS((abstr1 -- int) + z,concr1), CommonSubexpression),
                Partition(u, RHS((abstr2 -- int) + z,concr2), CommonSubexpression))
          case None =>
            if(rhs1 == rhsCommon)
              Set(Partition(u, RHS((abstr2 -- int) + v, concr2), CommonSubexpression))
            else if(rhs2 == rhsCommon)
              Set(Partition(v, RHS((abstr1 -- int) + u, concr1), CommonSubexpression))
            else {
              val z = fresh(Loc.builtin, none, Ambiguous(Free), Rho(Loc.builtin))
              Set(Partition(z, rhsCommon, CommonSubexpression),
                  Partition(v, RHS((abstr1 -- int) + z, concr1), CommonSubexpression),
                  Partition(u, RHS((abstr2 -- int) + z, concr2), CommonSubexpression))
            }
        }
    }

  /* Disjunction
   * r1 <- A* a*       P* z+ C* c* S* s*
   * r2 <- A* a* R* r*       C* c* T* t*
   * r2 <- A* a* R* r* P* z+    u+ U*
   * C* c* non-empty
   * --------------------------------------
   * u+ <- C* c* v (v fresh)
   */
  def disjunction(rhs1: RHS, rhs2: RHS, rhs3: RHS)(implicit su: Supply): Set[Partition] = {
    val RHS(abs1, con1) = rhs1
    val RHS(abs2, con2) = rhs2
    val RHS(abs3, con3) = rhs3

    val conAll = con1 intersect con2 intersect con3
    val absAll = abs1 intersect abs2 intersect abs3
    val conC = (con1 intersect con2) -- conAll
    val absc = (abs1 intersect abs2) -- absAll
    val absr = (abs2 intersect abs3) -- absAll
    val absz = (abs1 intersect abs3) -- absAll
    val absu = abs3 -- absz -- absr -- absAll

    val v = fresh(Loc.builtin, none, Ambiguous(Free), Rho(Loc.builtin))

    val r : Set[Partition] = if(absz.isEmpty || (conC.isEmpty && absc.isEmpty)) Set()
            else absu.size match {
              case 0 => Set()
              case 1 =>
                val u = absu.head
                Set(Partition(u, RHS(absc + v, conC), Disjunction))
              case _ =>
                val us = fresh(Loc.builtin, none, Ambiguous(Free), Rho(Loc.builtin))
                Set(Partition(us, RHSAbstr(absu), Disjunction), Partition(us, RHS(absc + v, conC), Disjunction))
            }
//    if(r.nonEmpty) {
//      System.err.println("RHS1: " + rhs1)
//      System.err.println("RHS2: " + rhs2)
//      System.err.println("RHS3: " + rhs3)
//      System.err.println("Inferred")
//      r.foreach(System.err.println(_))
//      System.err.println("-----")
//    }
    r
  }
}
