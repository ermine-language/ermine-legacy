package com.clarifi.reporting

import java.util.concurrent.{
  Executors, ExecutorService, LinkedBlockingQueue, ThreadFactory
}

import scalaz._
import scalaz.effect.IO
import IO._
import Kleisli._
import syntax.id._
//
import syntax.traverse.{ToFunctorOps => _, _}
import syntax.monad._
import std.stream._

import com.clarifi.reporting.Reporting._
import com.clarifi.reporting.util.StreamTUtils
import Id._

abstract class Backend[M[+_]](implicit mon: Monad[M]) {
  import Backend._

  val M = mon

  lazy val eta: Id ~> M = new (Id ~> M) {
    def apply[A](a: A) = M.pure(a)
  }

  type KS[A] = Kleisli[M, Source, A]

  final type G[A] = Kleisli[M, Source, A]

  // TODO: Require being able to retrieve a relation of (RefID, Type) tuples.
  //def refs: Relation[Type]

  /** Creates a table with the given RefID and Header and returns the RefID. */
  def create(id: RefID, header: Header, hints: TableHints, schemaHints: Hints): G[RefID]

  /** Dump a dataset into a collection of tables.
    * @param schema - map of meaningful table names to (materialized name, header) pair.
    */
  def populateSchema(schema: Map[TableName,(RefID,Header)], records: DataSet, batchSize: Int = 5000): G[Unit] =
    populateSchemaM(schema, M.pure(records), batchSize)

  def populateSchemaM(schema: Map[TableName,(RefID,Header)], records: M[DataSet], batchSize: Int = 5000): G[Unit] =
    Kleisli(s => ^(schemaPopulator(schema, s, batchSize), records){(iv, tups) =>
      applyIOIteratee(tups, batchSize)(iv._1, iv._2, iv._3).unsafePerformIO
    })

  private val iodetrans: IO ~> Id = new ~>[IO, Id] {
    def apply[A](x: IO[A]): A = x.unsafePerformIO
  }

  /** Chunk `xs` by Vectors of `batchSize/4` and yield it all in another
    * thread, delivering chunks, maximum 8 at a time, to this thread,
    * which runs `pre`, all of `iv`, and `post`.
    */
  private def applyIOIteratee[E, A](xs: StreamT[Id, E], batchSize: Int
                                  )(pre: IO[Unit], iv: scalaz.Iteratee[IO, E, A], post: IO[Unit]): IO[A] = {
    type Q = LinkedBlockingQueue[Option[Exception] Either Vector[E]]
    @annotation.tailrec
    def rec(iv: IterV[E, A], xss: Q): A =
      xss.take() match {
        case Right(x) => rec(iv(x), xss)
        case Left(None) => iv.run
        case Left(Some(e)) => throw e
      }
    pre *> (iv.lower(iodetrans) map {iv =>
              val q = new Q(8)
              executor submit runnable{
                var fail = false
                try {
                  StreamTUtils.foreach{
                    StreamTUtils.chunk[E, Vector[E], Id]((batchSize / 4) max 16, xs)
                  }(x => q put Right(x))
                } catch {case e: Exception => q put Left(Some(e)); fail = true}
                finally {if (!fail) q put Left(None) else ()}
              }
              rec(iv, q)
            }) <* post
  }

  def schemaPopulator(schema: Map[TableName,(RefID,Header)], s: Source, batchSize: Int = 5000): M[(IO[Unit], Iteratee[IO, (TableName, Record), Unit], IO[Unit])]

  /**
   * Create the indicies on a collection of tables, given a set of hints.
   */
  def createIndices(schema: Map[TableName, (RefID, Header)], hints: Hints): G[Unit]

  // todo - remove me once scalaz gets updated
  import StreamTUtils._

  def insertAll(id: RefID, header: Header, e: StreamT[Id,Record], batchSize: Int = 5000): G[Unit] =
    insertAllM(id, header, M.pure(e), batchSize)

  def insertAllM(id: RefID, header: Header, e: M[StreamT[Id,Record]], batchSize: Int = 5000): G[Unit] = {
    val tname = TableName("dontcare", Nil)
    populateSchemaM(Map((tname, (id,header))), e map (_.map (t => (tname, t))))
  }

  /** Create a collection of tables, using the given strategy for mapping meaningful table names
    * to materialized table names. Returns a Map of the created tables, indexed by their
    * meaningful names. */
  def createSchema(toRefID: TableName => RefID, headers: Map[TableName,(Header,TableHints)]):
  G[Map[TableName,(RefID,Header)]] = {
    reverseTopSort[TableName](headers.keys.toStream)(tn => headers(tn)._2.foreignKeys.keys.toStream).map(tname => {
      val (hdr,hints) = headers(tname)
      val tbl: G[RefID] = create(toRefID(tname), hdr, hints, Hints(headers.mapValues(_._2)))
      tbl.map(rid => (tname, (rid, hdr))): G[(TableName, (RefID, Header))]
    }).sequence[KS, (TableName,(RefID, Header))].map(kvs => Map(kvs: _*))
  }

  // Bulk load a relation from tuples

  def load[A](id: RefID, header: Header, e: StreamT[Id,Record], batchSize: Int): G[TableName] =
    loadM(id, header, M.pure(e), batchSize)

  def loadM[A](id: RefID, header: Header, e: M[StreamT[Id,Record]], batchSize: Int): G[TableName] = {
    for {
      ref <- create(id, header, TableHints.empty, Hints.empty)
      _ <- insertAllM(ref, header, e, batchSize)
      src <- ask[M, Source]
    } yield ref
  }

  def load[A](header: Header, e: StreamT[Id,Record], batchSize: Int = 1000): G[TableName] =
    loadM(header, M.pure(e), batchSize)

  def loadM[A](header: Header, e: M[StreamT[Id,Record]], batchSize: Int = 1000): G[TableName] =
    newRefID flatMap (id => loadM(id, header, e, batchSize))

  import IterV._

  def loadRecords[A](h: Header, s: Source): M[(IO[Unit], Iteratee[IO, Record, TableName], IO[Unit])] =
    for {
      i <- newRefID(s)
      ref <- create(i, h, TableHints.empty, Hints.empty)(s)
      imbox <- schemaPopulator(Map(TableName(i.toString) -> (i, h)), s)
      (pre, im, post) = imbox
    } yield (pre,
             im.xmap((x: Record) => (TableName(i.toString), x), (x: (TableName, Record)) => x._2).
                map(_ => ref),
             post)

  // Generate a unique reference
  def newRefID: G[RefID]

  // Discard a reference
  def destroy(r: RefID): G[Unit]

}

object Backend {
  val executor: ExecutorService =
    Executors newCachedThreadPool {
      new ThreadFactory {
        def newThread(r: Runnable) = {
          val t = Executors.defaultThreadFactory newThread r
          t setDaemon true
          t
        }
      }}

  private def runnable(f: => Unit) = new Runnable{def run = f}

  private implicit val vecEnumerator: Enumerator[Vector] = new Enumerator[Vector] {
    def apply[E, A](f: Vector[E], i: IterV[E, A]): IterV[E, A] = {
      @annotation.tailrec
      def rec(ix: Int, i: IterV[E, A]): IterV[E, A] =
        if (ix >= f.size) i
        else i.fold(done = (a, e) => Left(IterV.Done(a, e)),
                    cont = k => Right(k(IterV.El(f(ix))))) match {
          case Left(a) => a
          case Right(ivr) => rec(ix + 1, ivr)
        }
      rec(0, i)
    }
  }
}
