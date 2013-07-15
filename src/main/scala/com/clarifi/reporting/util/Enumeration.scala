package com.clarifi.reporting.util

import scalaz._
import Scalaz._
import IterV._

/** A producer of elements of type A. */
  trait Enumeration[A] {

    /** Return the head and tail of this Enumeration, if it exists. */
    def uncons: Option[(A,Enumeration[A])]

    def head: A = uncons.getOrElse(sys.error("Cannot get head of an empty enumeration"))._1

    /** Feeds all elements in this Enumeration to the given Iteratee. */
    def apply[B](i: IterV[A,B]): IterV[A,B] = {
      def go(e: Enumeration[A], i: IterV[A,B]): IterV[A,B] =
        i fold (
          (b,ia) => Done(b,ia),
          cont => e.uncons match {
            // need to use pattern matching here to get tail recursion
            case Some((h,t)) => go(t, cont(El(h)))
            case _ => i
          }
        )
      go(this, i)
    }

    /** Feeds all elements in this Enumeration to the given monadic Iteratee. */
    def apply[M[+_],B](i: Iteratee[M,A,B])(implicit m: Monad[M]): Iteratee[M,A,B] = {
      def go(e: Enumeration[A], i: Iteratee[M,A,B]): Iteratee[M,A,B] =
        Iteratee[M,A,B](
          i.value flatMap (itervm => itervm fold (
            (b,ia) => DoneM[M,A,B](b,ia).pure[M],
            cont => e.uncons match {
              // need to use pattern matching here to get tail recursion
              case Some((h,t)) => go(t, cont(El(h))).value
              case _ => i.value
            }
          ))
        )
      go(this, i)
    }

    /** Concatenates sources. */
    def ++(e: Enumeration[A]): Enumeration[A] = new Enumeration[A] {
      def uncons: Option[(A,Enumeration[A])] =
        Enumeration.this.uncons match {
          case None => e.uncons
          case Some((h,t)) => Some((h, t ++ e))
        }
    }

    /** Transforms the output of this producer. */
    def map[B](f: A => B): Enumeration[B] = new Enumeration[B] {
      def uncons: Option[(B,Enumeration[B])] =
        Enumeration.this.uncons match {
          case None => None
          case Some((h,t)) => Some((f(h), t.map(f)))
        }
    }

    /** Combines corresponding elements in both producers, stopping when either runs out. */
    def zip[B](e: Enumeration[B]): Enumeration[(A,B)] = new Enumeration[(A,B)] {
      def uncons: Option[((A,B),Enumeration[(A,B)])] =
        Enumeration.this.uncons match {
          case None => None
          case Some((ha,ta)) => e.uncons match {
            case None => None
            case Some((hb,tb)) => Some((ha,hb),(ta zip tb))
          }
        }
    }

    /** Combines each element in the producer with its index, stopping when the producer runs out. */
    def zipWithIndex: Enumeration[(A,Int)] = zip(Enumeration.from(0))

    /**
     * Map followed by concatenation. This method is carefully written
     * to ensure each Enumeration[B] can be garbage collected after
     * its elements have been pushed to the Iteratee.
     */
    def flatMap[B](f: A => Enumeration[B]): Enumeration[B] = new Enumeration[B] {
      def uncons: Option[(B,Enumeration[B])] =
        Enumeration.this.uncons match {
          case None => None
          case Some((ha,ta)) => f(ha).uncons match {
            case None => ta.flatMap(f).uncons // no Bs for this A
            case Some((hb,tb)) => Some((hb, ta.flatMap(f) ++ tb))
          }
        }
    }


    def toStream: Stream[A] = uncons.map{ case(x, xs) => x #:: xs.toStream }.getOrElse(Stream.empty)

    def toList: List[A]= toStream.toList

    def toSet: Set[A] = toStream.toSet

    def isEmpty: Boolean = !uncons.isDefined

    def traverse[B, M[_]:Applicative](f: A => M[B]): M[Enumeration[B]] = uncons.traverse {
      case(x, xs) => (f(x) |@| xs.traverse(f))((_,_))
    }.map(op => new Enumeration[B] { def uncons = op })

    /** Return the Cartesian product of this Enumeration with the specifed other Enumeration. */
    def product[B](other: Enumeration[B]): Enumeration[(A, B)] = for {
      a <- this
      b <- other
    } yield (a, b)

    def filter(pred: A => Boolean): Enumeration[A] = new Enumeration[A] {
      def uncons = {
        var cur = Enumeration.this.uncons
        while (cur.isDefined && !pred(cur.get._1)) {
          cur = cur.get._2.uncons
        }
        cur map { case (h,t) => (h, t filter pred) }
      }
    }

    /**
     * Split this enumeration into a pair of Enumerations.
     * The elements of the first Enumeration satisfy the predicate; the elements of the second do not.
     */
    def partition(pred: A => Boolean): (Enumeration[A], Enumeration[A]) = (filter(pred), filter(!pred(_)))

    def unzipMap[K](keys: Map[K,A => Boolean]): Map[K,Enumeration[A]] =
      keys.mapValues(filter)

    def foreach(f: A => Unit): Unit = {
      var cur = this
      var c = cur.uncons
      while (c.isDefined) {
        val ht = c.get
        f(ht._1)
        cur = ht._2
        c = ht._2.uncons
      }
    }

    def length: Int = {
      var i = 0;
      foreach { _ => i = i + 1; Unit }
      i
    }
 }

object Enumeration {
  def nil[A] = new Enumeration[A] {
    def uncons: Option[(A, Enumeration[A])] = none
  }

  def singleton[A](x: A) = new Enumeration[A] {
    def uncons: Option[(A, Enumeration[A])] = some((x, nil))
  }

  def apply[A](as: A*): Enumeration[A] = make(as)

  /** Construct an Enumeration from an Interable. */
  def make[A](it: Iterable[A]): Enumeration[A] =  new Enumeration[A] {
    def uncons: Option[(A,Enumeration[A])] = {
      if (it.isEmpty) none
      else some((it.head, Enumeration.make(it.tail)))
    }
  }

  def unfold[S, A](s: S, f: (S => Option[(S, A)])): Enumeration[A] = {
    new Enumeration[A] {
      def uncons = f(s).map{ case (s2, a) => (a, unfold(s2, f)) }
    }
  }

  /** Return an infinitiely incrementing enumeration where the first value is z. */
  def from(z: Int):Enumeration[Int] = new Enumeration[Int] { def uncons = some( (z, from(z+1)) ) }

  implicit def Equal[A](implicit eqA: Equal[A]) = new Equal[Enumeration[A]] {
    def equal(e1: Enumeration[A], e2: Enumeration[A]): Boolean = {
      (e1.uncons, e2.uncons) match {
        case (None, None) => true
        case (None, Some(_)) => false
        case (Some(_), None) => false
        case (Some((h1, t1)), Some((h2, t2))) => if (h1 === h2) equal(t1, t2) else false
      }
    }
  }
}
