package com.clarifi.reporting

object Supply {
  val minSplitSupplySize = 32
  val blockSize = 1024
  private var block: Int = 0
  def getBlock = synchronized {
    val result = block;
    block = result + blockSize
    result
  }
  def create = {
    val b = getBlock
    new Supply(b, b + blockSize - 1)
  }
}

// each supply is accessed in a single threaded fashion, but they allocate globally unique ids
class Supply private(private var lo: Int, private var hi: Int) {

  import Supply._
  def fresh: Int = if (lo != hi) {
    val result = lo
    lo = result + 1
    result
  } else {
    val result = getBlock
    hi = result + blockSize - 1
    lo = result + 1
    result
  }

  def split: Supply = {
    if (hi - lo >= minSplitSupplySize) {
      val mid = lo + (hi - lo) / 2
      val result = new Supply(lo, mid)
      lo = mid + 1
      result
    } else {
      val newLo = getBlock
      lo = newLo + blockSize / 2
      hi = newLo + blockSize - 1
      new Supply(newLo, lo - 1)
    }
  }

}


// vim: set ts=4 sw=4 et:
