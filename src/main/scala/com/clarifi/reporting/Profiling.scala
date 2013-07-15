package com.clarifi.reporting

import collection.mutable.ArrayBuffer
import Profile.formatEntry

case class Profiling(times: ArrayBuffer[(String, Long)])  {
  def +=(p: (String, Long)) = times.synchronized { times += p }
  
  def clear = times.clear

  def summary = 
    "summary:\n" + 
    "  total: " + times.map(_._2).sum + "ms\n" + 
    "  top 5: \n" + 
    times.groupBy(_._1).mapValues(_.map(_._2).sum).toList.sortBy(_._2).reverse.
    take(5).map(formatEntry).mkString("\n") 

  def fullTrace =
    "full trace:\n------------------\n" +
    times.map(formatEntry).mkString("\n")

  override def toString = 
    summary + "\n\n" + fullTrace
}    

object Profile { 
  val instance = Profiling(ArrayBuffer())

  def formatEntry(p: (String, Long)): String = 
    p._2 + "ms: " + p._1
}
