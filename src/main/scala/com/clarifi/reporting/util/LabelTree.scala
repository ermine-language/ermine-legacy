package com.clarifi.reporting.util

import collection.immutable.IndexedSeq

import scalaz.NonEmptyList
import scalaz.NonEmptyList.nel

/**
 * Tree is a variable-arity tree with labeled child links and values at all nodes.
 *
 * @author JAT
 */
case class LabelTree[K, V](value: V, children: Map[K, LabelTree[K, V]]) {

  def asPathList: Stream[(List[K], V)] = {
    def helper(path: List[K], tree: LabelTree[K, V]): Stream[(List[K], V)] = 
      (path, value) #:: tree.children.toStream.flatMap(p => helper(p._1 :: path, p._2))
    helper(List(), this).map(p => (p._1.reverse, p._2))
  }

  def asPathNonEmptyList(rootName: K): Stream[(NonEmptyList[K], V)] = 
    asPathList map (p => (nel(rootName, p._1), p._2))
  
  def fromPathList(pathList: Enumeration[(List[K], V)]): LabelTree[K,V] = {
    // Sort by path length
    val sortedPathSeq = pathList.map((p:(List[K], V)) => (IndexedSeq(p._1: _*), p._2)).toStream.sortBy(_._1.length)
    val sortedPathList = sortedPathSeq.map((p:(IndexedSeq[K], V)) => (List(p._1: _*), p._2))
    val head = sortedPathList.head
    val tail = sortedPathList.tail
    // Insert nodes into the tree
    tail.foldLeft(LabelTree(head._2, Map()):LabelTree[K,V])((tree, pair) => tree.insert(pair._1, pair._2))
  }
  
  /**
   * Insert a new value into the tree.
   * Path is specified from root to location of new value.
   */
  def insert(path: List[K], newValue: V): LabelTree[K,V] = {
    path match {
      case List() => LabelTree(newValue, children) // Overwrite an existing value
      case head :: tail => LabelTree(value, 
                                     children + (head -> children.get(head).map(_.insert(tail, newValue)).getOrElse(
                                       if (!tail.isEmpty) sys.error("Path prefix not found in tree") 
                                       else LabelTree(newValue, Map())  // Insert new value at leaf
                                       )
                                     ))
    }
  }
}
