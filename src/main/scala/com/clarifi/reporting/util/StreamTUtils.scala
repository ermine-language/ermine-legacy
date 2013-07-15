package com.clarifi.reporting.util

import scalaz._
import scala.collection.immutable.{ Set }
import scalaz.Scalaz._
import scalaz.concurrent.{Promise, Strategy}

object StreamTUtils {
  import scalaz.StreamT._

  def make[F[_]:Foldable,A](s: F[A]): StreamT[Id,A] =
    s.foldr(empty[Id,A])(x => y => x :: y)

  def wrapEffect[M[+_]:Functor,A](m: M[StreamT[M,A]]): StreamT[M,A] =
    StreamT[M,A](m map { Skip[StreamT[M,A]](_) })

  def concatMapIterable[M[+_],A,B](m: Iterable[A])(f: A => StreamT[M,B])(implicit M: Applicative[M]): StreamT[M, B] =
    StreamT[M,B](
      if (m isEmpty) M.pure(Done)
      else M.pure(Skip(f(m.head) ++ concatMapIterable[M,A,B](m.tail)(f)))
    )

  def toStreamT[A](f: Iterable[A]): StreamT[Id,A] = StreamT[Id,A](
    if (f.isEmpty) Done
    else Yield(f.head, toStreamT(f.tail)))

  def toIterable[A](s: StreamT[Id,A]): Iterable[A] = new Iterable[A] {
    def iterator: Iterator[A] = new Iterator[A] {
      var cursor = s
      def hasNext: Boolean = !cursor.isEmpty
      def next: A = cursor.uncons
        .cata ({case (h, t) => cursor = t; h},
               throw new NoSuchElementException("next on empty stream"))
    }
  }

  /** Partition into `n`-sized chunks, each chunk represented with an
    * arbitrary strict Scala iterable.
    */
  def chunk[A, C <: Iterable[Any], M[+_]](n: Int, s: StreamT[Id, A]
          )(implicit cbf: collection.generic.CanBuildFrom[Nothing, A, C],
            M: Applicative[M]
          ): StreamT[M, C] = {
    def take(acc: collection.mutable.Builder[A, C], n: Int, s: StreamT[Id, A]
            ): (C, StreamT[Id, A]) =
      if (n <= 0) (acc.result(), s)
      else unconsId(s) match {
        case Some((a, s)) => take(acc += a, n - 1, s)
        case None => (acc.result(), s)
      }
    StreamT.unfoldM(s){s => take(cbf(), n, s).point[M] map {
                         case r if !r._1.isEmpty => Some(r)
                         case _ => None
                       }}
  }

  private def unchunk[A](s: StreamT[Id, Iterable[A]]): StreamT[Id, A] =
    s flatMap toStreamT

  /** Precache by one step. */
  private def precache[A](s: StreamT[Need, A]
                        )(implicit strat: Strategy): StreamT[Need, A] =
    StreamT.unfoldM(s){s =>
      val p = Promise(s.uncons.value)
      Need(p.get)
    }

  /** Chunked precalculation of a stream. */
  def precached[A](s: StreamT[Id, A], batchSize: Int
                 )(implicit strat: Strategy): StreamT[Id, A] =
    unchunk(StreamT.unfold(precache(chunk[A, Vector[A], Need](batchSize, s))){
              s => s.uncons.value
            })

  def unconsId[A](s: StreamT[Id,A]): Option[(A, StreamT[Id,A])] = s.step match {
    case Done => None
    case Skip(f) => unconsId(f())
    case Yield(a, f) => Some((a, f()))
  }

  def runStreamT_[S,A](as: StreamT[({type f[+x] = State[S,x]})#f, A])(s: S) = StreamT.runStreamT(as,s)
  def runStreamT[S:Monoid,A](as: StreamT[({type f[+x] = State[S,x]})#f, A]) = StreamT.runStreamT(as,mzero[S])

  type Forest[A] = Stream[Tree[A]]
  import Tree._

  def generate[A](children: A => Stream[A], a: A): Tree[A] =
    node(a, children(a).map(b => generate(children, b)))

  def chop[A](forest: Forest[A]) : State[Set[A], Forest[A]] = forest match {
    case Node(v,ts) #:: us =>
      for {
        s <- init
        a <- if (s contains v) chop(us)
             else for {
               _  <- put(s + v)
               as <- chop(ts)
               bs <- chop(us)
             } yield node(v,as) #:: bs
      } yield a
    case _ => Stream().pure[({type S[+x] = State[Set[A],x]})#S]
  }

  def prune[A](forest: Forest[A]): Forest[A] = chop(forest) eval Set()

  def dfs[A](children: A => Stream[A], vs: Stream[A]) : Forest[A] = prune(vs.map(generate(children,_)))

  def postOrder[A](tree : Tree[A]): Stream[A] = tree match {
    case Node(a,ts) => ts.flatMap(postOrder) ++ Stream(a)
  }

  def reverseTopSort[A](vertices: Stream[A])(children: A => Stream[A]): Stream[A] =
    dfs(children, vertices) flatMap postOrder

  def foreach[A](aas: StreamT[Id, A])(f: A => Unit): Unit = aas.step match {
    case Yield(a,as) => { f(a); foreach[A](as())(f); }
    case Skip(as) => foreach[A](as())(f)
    case Done => ()
  }

}
