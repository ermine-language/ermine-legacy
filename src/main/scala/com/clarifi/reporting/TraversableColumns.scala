package com.clarifi.reporting

import scalaz.{Applicative, Monoid}
import scalaz.Id._
import scalaz.std.list._
import scalaz.std.set._
import scalaz.std.vector._
import scalaz.syntax.apply._
import scalaz.syntax.semigroup._

trait TraversableColumns[E <: TraversableColumns[E]] {self: E =>
  /** Traversal over columns in `E` (myself). */
  def traverseColumns[F[+_]: Applicative](f: ColumnName => F[ColumnName]): F[E]

  /** @note May not contain all of `foldMap`. */
  def typedColumnFoldMap[Z: Monoid](f: (ColumnName, PrimT) => Z): Z

  /** Answer the columns that `E` uses. */
  def columnReferences: Set[ColumnName] =
    foldMap(Set(_))

  /** Answer typed columns that `E` uses.
    *
    * @note May not contain all `columnReferences`.
    */
  def typedColumnReferencesList: List[(ColumnName, PrimT)] =
    typedColumnFoldMap((n, t) => Vector((n, t))).toList

  /** Answer columns that `E` uses, with duplicates and in order. */
  def columnReferencesList: List[ColumnName] =
    foldMap(List(_))

  /** Replace column names in `E`. */
  def mapColumns(f: ColumnName => ColumnName) =
    traverseColumns[Id](f)

  def foldMap[M: Monoid](f: ColumnName => M): M =
    traverseColumns[({type λ[+α] = M})#λ](f)

  /** Column traversals can be sequenced. */
  def columnsProduct[OE <: TraversableColumns[OE]](other: OE):
      TraversableColumns.Product[E, OE] = TraversableColumns.Product(self, other)
}

object TraversableColumns {
  case class Product[A <: TraversableColumns[A], B <: TraversableColumns[B]
                   ](_1: A, _2: B)
       extends Product2[A, B] with TraversableColumns[Product[A, B]] {
    def traverseColumns[F[+_]: Applicative](f: ColumnName => F[ColumnName]):
        F[Product[A, B]] =
      ^(_1 traverseColumns f, _2 traverseColumns f)(Product.apply)

    def typedColumnFoldMap[Z: Monoid](f: (ColumnName, PrimT) => Z): Z =
      _1.typedColumnFoldMap(f) |+| _2.typedColumnFoldMap(f)
  }
}
