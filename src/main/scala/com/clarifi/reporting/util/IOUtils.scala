package com.clarifi.reporting.util

import java.io.{File, OutputStream, InputStream}


object IOUtils {
  /**
   * Read all the data from the given InputStream
   * and copy it to the given OutputStream.
   * @return the number of bytes read and sent
   */
  def copy(input:InputStream, output:OutputStream, defaultBufferSize:Int=(256), closeInputStream:Boolean=true): Long = try {
    val buffer = new Array[Byte](defaultBufferSize)
    var count = 0L
    var n = input.read(buffer)
    while (n != -1) {
      output.write(buffer, 0, n)
      count += n
      n = input.read(buffer)
    }
    count
  } finally if (closeInputStream) input.close()

  /**
   * Tries to find a file. If it exists, returns Some(file). If not, None.
   */
  def findFile(name:String): Option[File] = {
    val f = new File(name)
    if(f.exists) Some(f) else None
  }

  /**
   * Reads the contents of the given file.
   * @throws FileNotFoundException if the file doesn't exist.
   */
  def slurp(fileName:String): String = {
    val source = scala.io.Source.fromFile(fileName, "UTF-8")
    val str = source.mkString
    source.close
    str
  }
}
