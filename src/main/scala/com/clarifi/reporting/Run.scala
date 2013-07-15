package com.clarifi.reporting

/** A G-algebra for "running" a value in G
  * where G is usually some monad.
  *
  * @note identity law: run(fa) == run(run(fa).point[G]) | Applicative[G]
  * @note distributive law: run(f)(run(fa)) == run(fa <*> f) | Apply[G]
  */
trait Run[G[_]] {
  def run[A](a: G[A]): A
}
