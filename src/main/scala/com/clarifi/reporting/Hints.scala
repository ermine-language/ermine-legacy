package com.clarifi.reporting

import collection.immutable.SortedSet
import scala.util.control.NonFatal

import Reporting._
import Reporting.alignMap
import scalaz.Scalaz._
import scalaz.std.indexedSeq._

/** Type aliases and utility functions for building Hints. */
object Hints {
  type ColumnGroup = SortedSet[ColumnName]
  type IsCandidateKey = Boolean
  // Set(("foo","bar")) is a simple foreign key
  // Set(("foo","bar"), ("index","ind")) is a complex foreign key
  type ForeignKey = SortedSet[(ColumnName, ColumnName)]
  
  /** The empty Hints object. */
  val empty = Hints(Map())

  /** Constructor for Hints objects - adds TableHints.empty as the default hints for each table. */
  def apply(tables: Map[TableName,TableHints]): Hints = 
    new Hints(tables.withDefaultValue(TableHints.empty))
}

import Hints._

/** Class for holding and manipulating per-table hints information. */
class Hints private(val tables: Map[TableName,TableHints]) {
  
  /** Adds table hints for the given table name - this will overwrite any previous hints for this table name. */
  def +(tnh: (TableName,TableHints)): Hints = 
    Hints(tables + tnh) 

  /** Adds a primary key to the given table and adds the column group as an index. */
  def withPK(t: TableName, pk: ColumnGroup): Hints = 
    Hints(tables + (t -> tables.getOrElse(t, TableHints.empty).withPK(pk)))
  def withPK(t: TableName, pk: ColumnName): Hints = 
    withPK(t, SortedSet(pk))

  /** Adds a foreign key constraint to the referer table (it references columns in referent). */
  def withFK(referer: TableName, referent: TableName, fk: ForeignKey): Hints = 
    Hints(tables + (referer -> tables.getOrElse(referer, TableHints.empty).withFK(referent, fk)))
  def withFK(referer: TableName, col1: ColumnName, referent: TableName, col2: ColumnName): Hints = 
    withFK(referer, referent, SortedSet((col1,col2))) 

  /** Adds an index to the given table. */
  def withIndex(t: TableName, c: ColumnGroup, b: IsCandidateKey): Hints = 
    Hints(tables + (t -> tables.getOrElse(t, TableHints.empty).withIndex(c, b)))
  def withIndex(t: TableName, c: ColumnName, b: IsCandidateKey): Hints = 
    withIndex(t, SortedSet(c), b) 

  /** Transform the hints for all the given tables using the specified function. */
  def rehintAll(tbls: Iterable[TableName], f: TableHints => TableHints): Hints =
    rehintAll(tbls, (_,th) => f(th))

  def rehintAll(tbls: Iterable[TableName], f: (TableName, TableHints) => TableHints): Hints =
    Hints(tbls.toSet.foldLeft(tables)((tables,t) => tables + (t -> f(t,tables(t)))))

  def rename(from: TableName, to: TableName): Hints = 
    Hints(tables - from ++ tables.get(from).map((to,_)) mapValues (_.renameTable(from, to)))
  
  def drop(t: TableName): Hints = Hints(tables - t)

  /** Join of the two Hints objects. Colliding tables are combined using TableHints.join. */
  def join(h: Hints) = Hints(alignMap(tables, h.tables)(th => th, th => th, _ join _))

  /** Union of the two Hints objects. Colliding tables are combined using TableHints.union. */
  def union(h: Hints) = Hints(alignMap(tables, h.tables)(th => th, th => th, _ union _))
  
  /** Ensures that all table and column names mentioned in this Hints object are consistent 
    * with table and column names mentioned in h.
    */
  def check(h: Map[TableName,Header]): Hints = 
    try {
      if (!(tables.keySet.toSet -- h.keySet).isEmpty) sys.error("table sets do not match")
      h.foreach(kv => tables.get(kv._1).foreach(th => if (!th.check(kv._2, h)) sys.error("table is invalid: " + kv._1)))
      this
    } catch { case NonFatal(e) => 
      println("Invalid hints with respect to headers:\n" + h.mkString("\n----\n") + "\n" + tables.mkString("\n"))
      throw e
    }

  /** Ensures that foreign keys are references to primary keys in the foreign tables. */
  def checkFKs: Hints = {
    tables.values.forall(th => th.foreignKeys.forall { case (ft,fks) => 
      val pkf: ColumnGroup = tables.getOrElse(ft, sys.error("table " + ft + " doesn't exist")).primaryKey.getOrElse(
        sys.error("foreign table does not have primary key " + ft)) 
      fks.map(_.map(_._2)).forall(fkcols => fkcols == pkf || 
        sys.error("fkcols did not equal primary key columns of foreign table: " + ((ft,fkcols, pkf))))
    })
    this
  }

  override def toString = "Hints:\n" + tables.mkString("\n")

  def mapNames(f: TableName => TableName) = new Hints(tables.map{ case (k, v) => (f(k), v.mapNames(f)) })
}

object TableHints {
  /** The empty TableHints object. */
  val empty = TableHints(None, Map(), Map(), List())
}

/** Struct with hints to the backend about how to store and access 
  * the data in this table efficiently. 
  * @todo - possibly add support for encoding hints like RLE encoding, etc
  */
// TODO: add an isRoot : Boolean hint
case class TableHints private(
  primaryKey: Option[ColumnGroup],
  indices: Map[ColumnGroup,IsCandidateKey],
  foreignKeys: Map[TableName, Set[ForeignKey]], // key is the foreign table, value is Set[(localCol, foreignCol)]
  sortOrder: List[(ColumnName,ColumnName)]) { // list of pairs where the first column in the pair should come before the second

  def mapNames(f: TableName => TableName) = TableHints(primaryKey, indices, foreignKeys.map{ case (k, v) => (f(k), v) }, sortOrder)

  /** A hints object for the join of these two tables. */
  def join(t: TableHints) = TableHints(
    ^(primaryKey, t.primaryKey)(_ ++ _), // concatenate the two PKs - if either is None, join is None
    { 
      val candidates1: Set[ColumnGroup] = indices.filter(_._2).map(_._1).toSet
      val candidates2: Set[ColumnGroup] = t.indices.filter(_._2).map(_._1).toSet
      // cartesian product of all candidate keys
      ^(candidates1.toIndexedSeq,
        candidates2.toIndexedSeq)(_ ++ _).map((cg: ColumnGroup) => (cg,true)) ++
      // include all other indices too, but strip candidate key status
      indices.mapValues(_ => false) ++
      t.indices.mapValues(_ => false) toMap
    },
    // in case of collision, either hints can indicate FK for it to be a valid FK in the result
    alignMap(foreignKeys, t.foreignKeys)(a => a, b => b, (a,b) => a ++ b),
    (sortOrder ++ t.sortOrder).distinct
  )

  /** Reorder the columns referenced by this table to the given total order of columns. This discards any
    * previous order given to the columns in this table. */
  def reorder(columns: List[ColumnName]): TableHints =
    TableHints(primaryKey, indices, foreignKeys, for {
      (c1,i) <- columns.zipWithIndex
      (c2,j) <- columns.zipWithIndex
      if i < j
    } yield (c1,c2))

  def withOrderings(first: collection.Set[ColumnName], second: collection.Set[ColumnName]) = TableHints(
    primaryKey, indices, foreignKeys, (sortOrder ++ first.flatMap(a => second.map((a,_)))).distinct)

  /** Combine all indices and foreign keys using left-biased union. */
  def union(t: TableHints): TableHints = TableHints(
    // arbitrarily biased to stick with our PK 
    primaryKey orElse t.primaryKey, 
    // in case of collision, index is candidate key only if both are CKs
    alignMap(indices, t.indices)(a => a, b => b, _ && _), 
    // in case of collision, BOTH hints must indicate FK for it to be valid
    alignMap(foreignKeys, t.foreignKeys)(a => a, b => b, (a,b) => a intersect b), 
    (sortOrder ++ t.sortOrder).distinct)

  def withPK(pk: ColumnGroup): TableHints = 
    this.copy(primaryKey = Some(pk))

  def extendPK(pke: ColumnGroup): TableHints =
    this.copy(primaryKey = this.primaryKey map (pk => pk ++ pke) orElse Some(pke))
  
  def withFK(t: TableName, fk: ForeignKey): TableHints =
    this.copy(foreignKeys = this.foreignKeys + (t -> (this.foreignKeys.getOrElse(t, Set()) + fk)))

  def mapFKs(f: (TableName,ForeignKey) => ForeignKey): TableHints = 
    this.copy(foreignKeys = this.foreignKeys.transform((tn,fks) => fks map (fk => f(tn,fk))))

  def withIndex(cols: ColumnGroup, b: IsCandidateKey): TableHints = 
    this.copy(indices = this.indices + (cols -> b))

  /** Bulk update of column groups in indices and in primary key. */
  def reindex(f: ColumnGroup => ColumnGroup): TableHints = 
    this.copy(primaryKey = this.primaryKey map f, 
              indices = this.indices.map(p => (f(p._1), p._2)))

  def rename(f: ColumnName => ColumnName): TableHints = 
    TableHints(primaryKey = this.primaryKey map (_ map f),
               indices = this.indices.map(p => (p._1 map f, p._2)),
               foreignKeys = this.foreignKeys.mapValues(fks => fks map (_ map (ab => (f(ab._1), ab._2)))),
               sortOrder = this.sortOrder map { case (a,b) => (f(a), f(b)) })

  def renameTable(from: TableName, to: TableName): TableHints = 
    this.copy(foreignKeys = this.foreignKeys ++ this.foreignKeys.get(from).map(fks => (to, fks)))

  /** Checks several invariants. Essentially, makes sure that all table and
    * column names are consistent with those mentioned in hdrs. 
    */
  def check(h: Header, hdrs: Map[TableName,Header]): Boolean = 
    primaryKey.map(cg => (cg -- h.keySet).isEmpty).getOrElse(true) &&
    indices.toList.map(_._1).forall(cg => (cg -- h.keySet).isEmpty) &&
    (sortOrder.flatMap(p => List(p._1,p._2)).toSet -- h.keySet).isEmpty &&
    foreignKeys.forall(kv => kv._2.forall(fk => {
      val thisCols = fk.map(_._1)
      val otherCols = fk.map(_._2)
      (thisCols -- h.keySet).isEmpty &&
      (otherCols -- hdrs(kv._1).keySet).isEmpty
    }))
  
  /**
   * Takes a header and returns a list of the ColumnNames, in order the that they
   * should be created in the table.  Order is primary keys, then other candidate
   * keys, then index columns, then everything else.
   */
  def sortColumns(cols: collection.Set[ColumnName]): List[ColumnName] = {
    import com.clarifi.reporting.util.StreamTUtils.reverseTopSort
    val (cks, ncks) = indices.partition(kv => kv._2)
    val pk = primaryKey.getOrElse(Set.empty)
    val ret = (pk.toList ++ cks.keySet.flatten ++ ncks.keySet.flatten ++ cols).distinct
    val r = reverseTopSort(ret.toStream)(col => sortOrder.collect { case (p,c) if p == col => c } toStream).filter(cols).toList.reverse
    r
  }
}

