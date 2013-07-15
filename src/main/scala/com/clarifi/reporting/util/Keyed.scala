package com.clarifi.reporting.util

/** The descriptions associated with some values of a type.
  *
  * @note It is usually beneficial to implement `inj`. */
trait Keyed[C[_], A] {
  /** Apply an injection to `A`. */
  def inj[B](f: A => B): C[B] =
    propagate(f andThen (Iterable(_)))

  /** Apply a partial injection to `A`, discarding undefined
    * results. */
  def injColl[B](pf: PartialFunction[A, B]): C[B] =
    propagate(pf.lift andThen (_.toIterable))

  /** Apply an inverse function to `A`.
    *
    * @note invariant: ∀x,y∈A. x≠y ⇒ `f`(x)∩`f`(y)=∅. */
  def propagate[B](f: A => Iterable[B]): C[B]

  /** Overwrite me in the domain of `ren` with the range of `ren`,
    * erasing any information about that range I have. */
  def replaceKeys(ren: PartialFunction[A, A]): C[A]

  /** Erase information about non-`keys`. */
  def filterKeys(keys: A => Boolean): C[A] =
    injColl{case k if keys(k) => k}
}
