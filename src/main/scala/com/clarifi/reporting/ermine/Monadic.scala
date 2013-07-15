package com.clarifi.reporting.ermine

object ++ {
  def unapply[A,B](p: (A,B)) = Some(p)
}

trait Scoped[+T[+_],+A] {
  def self: T[A]
  def scope(desc: String): T[A]
}

// an interface we use just to make sure that we implement all the same generic functionality between monads
trait Functorial[+T[+_],+A] {
  def self: T[A]
  def map[B](f: A => B): T[B]
  def as[B](b: => B): T[B] = map(_ => b)
  def skip: T[Unit] = as(())
}

trait Filtered[T[+_],+A] extends Functorial[T,A] {
  implicit def lift[B](v: T[B]): Filtered[T,B]
  def withFilter(p: A => Boolean): T[A]
  def filterMap[B](f: A => Option[B]) = map(f).withFilter(_.isDefined).map(_.get)
  def filter(p: A => Boolean): T[A] = withFilter(p)
  def collect[B](f: PartialFunction[A,B]): T[B] = withFilter(f.isDefinedAt(_)) map f
}

trait AppliedOnce[T[+_],+A] extends Functorial[T,A] { that =>
  def map2[B,C](m: => T[B])(f: (A,B) => C): T[C]
  def ++[B](m: => T[B]): T[(A,B)] = map2(m)((_,_))
  def >>[B](m: => T[B]): T[B] = map2(m)((_,b) => b)
  def <<(m: => T[Any]): T[A]  = map2(m)((a,_) => a)
}

trait Applied[T[+_],+A] extends AppliedOnce[T,A] { that =>
  implicit def lift[B](v: T[B]): Applied[T,B]
  def between(bra: T[Any], ket: T[Any]) = bra >> (<<(ket))
}

trait Alternating[T[+_],+A] extends Applied[T,A] with Filtered[T,A] {
  implicit def lift[B](v: T[B]): Alternating[T,B]
  def |[B>:A](m: => T[B]): T[B]
  def orElse[B>:A](m: => B): T[B]
  def optional: T[Option[A]] = map(Some(_)).orElse(None)
  def skipOptional: T[Unit] = skip orElse ()
  def many: T[List[A]] = some orElse List()
  def some: T[List[A]] = map2(many)(_::_)
  def skipMany: T[Unit] = skipSome orElse ()
  def skipSome: T[Unit] = >>(skipMany)
  def sepBy(sep: T[Any]): T[List[A]] = sepBy1(sep) orElse List()
  def sepBy1(sep: T[Any]): T[List[A]] = map2((sep >> self).many)(_::_)
  def skipSepBy(sep: T[Any]): T[Unit] = skipSepBy1(sep) orElse ()
  def skipSepBy1(sep: T[Any]): T[Unit] = (sep >> self).skipMany
  def chainr[B>:A](op: T[(B,B) => B]): T[B] =
    map2(op.map2[B, B => B](chainr(op))((f,x) => y => f(y,x)) orElse ((x: B) => x))((b,f) => f(b))
  def chainl[B>:A](op: T[(B,B) => B]): T[B] = {
    def rest: T[B => B] = op.map2[B, B => B](self)((f,x) => y => f(y,x)).map2(rest)((fp, g) => g compose fp) orElse ((x: B) => x)
    map2(rest)((b,f) => f(b))
  }
  def manyTill(end: T[Any]): T[List[A]] = (end as List()) | map2(manyTill(end))(_::_)
  def skipManyTill(end: T[Any]): T[Unit] = end.skip | >>(skipManyTill(end))
  def endBy1(sep: T[Any]): T[List[A]] = <<(sep).some
  def endBy(sep: T[Any]): T[List[A]] = <<(sep).many
  def skipEndBy1(sep: T[Any]): T[Unit] = <<(sep).skipSome
  def skipEndBy(sep: T[Any]): T[Unit] = <<(sep).skipMany
  def sepEndBy1(sep: T[Any]): T[List[A]] =
    map2((sep >> sepEndBy(sep)).map(as => (a: A) => a :: as) orElse ((a: A) => List(a)))((b,f) => f(b))
  def sepEndBy(sep: T[Any]): T[List[A]] = sepEndBy1(sep) orElse List()
  def skipSepEndBy1(sep: T[Any]): T[Unit] = >>((sep >> skipSepEndBy(sep)) orElse ())
  def skipSepEndBy(sep: T[Any]): T[Unit] = skipSepEndBy1(sep) orElse ()
}

// technically these are mostly semigroupoid-like structures, because we don't offer unit directly
trait Monadic[T[+_],+A] extends Applied[T,A] {
  implicit def lift[B](v: T[B]): Monadic[T,B]
  def flatMap[B](f: A => T[B]): T[B]
  def map2[B,C](m: => T[B])(f: (A,B) => C): T[C] = flatMap(a => m.map(b => f(a,b)))
  override def >>[B](m: => T[B]): T[B] = flatMap(_ => m)
  override def <<(m: => T[Any]): T[A] = flatMap(m as _)
  def when(b: Boolean): T[Unit]
  def unless(b: Boolean): T[Unit] = when(!b)
}

trait MonadicPlus[T[+_],+A] extends Monadic[T,A] with Alternating[T,A] {
  implicit def lift[B](v: T[B]): MonadicPlus[T,B]
  def flatMatch[B](f: PartialFunction[A,T[B]]) = withFilter(f.isDefinedAt(_)) flatMap f
}

trait Comonadic[T[+_],+A] extends Functorial[T,A] {
  implicit def lift[B](v: T[B]): Comonadic[T,B]
  def map[B](f: A => B): T[B] = extend(ta => f(ta.extract))
  def extend[B](f: T[A] => B): T[B]
  def extract: A
}
