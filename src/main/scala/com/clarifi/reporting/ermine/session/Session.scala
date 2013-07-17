package com.clarifi.reporting
package ermine.session

import System.nanoTime
import java.text.DecimalFormat
import java.net.URL
import java.io.File
import java.io.File.{separator, separatorChar}
import scala.util.control.NonFatal
import com.clarifi.reporting.{ PrimT, Header, Source, TableName }
import com.clarifi.reporting.Reporting.{ RefID }
import com.clarifi.reporting.ermine.session.SessionTask._
import com.clarifi.reporting.ermine.session.Printer._
import java.util.Date
import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Relocatable.preserveLoc
import com.clarifi.reporting.ermine.Document._
import com.clarifi.reporting.ermine.Type.{
  Con, ffi, io, bool, subType, int, long, float, double, string, char, date, byte, short, field, Nullable, typeVars,
  allTypeVars, True, False, AliasExpanded, Bad, Expanded, Unexpanded, primTypes
}
import com.clarifi.reporting.ermine.Term.{ subTermEx, termVars }
import com.clarifi.reporting.ermine.HasTermVars._
import com.clarifi.reporting.ermine.Runtime.Thunk
import com.clarifi.reporting.ermine.Subst.{
  inferTypeDefKindSchemas, inferBindingGroupTypes, kindCheck, substType, inferType, solve,
  assertTypeClosed, assertTermClosed, unfurlApp
}
import com.clarifi.reporting.ermine.syntax._
import com.clarifi.reporting.ermine.syntax.TypeDef.typeDefComponents
import com.clarifi.reporting.ermine.parsing.{ phrase, ModuleHeader, ParseState, Parser }
import com.clarifi.reporting.ermine.parsing.ModuleParsers._
import com.clarifi.reporting.ermine.parsing.Err
import com.clarifi.reporting.ermine.parsing.TermParsers.term
import com.clarifi.reporting.relational._

import scala.io._
import scala.reflect._
import scalaz.Scalaz._
import scalaz.Monad
import scalaz.Free.{ suspend, Return, Trampoline }

import scala.collection.mutable.{HashMap, SynchronizedMap, ListBuffer}
import scala.collection.immutable.List

object Session {

  class Diagnostics {}
  private val _log = org.apache.log4j.Logger.getLogger(classOf[Diagnostics])

  type Stack = List[String]

  def subst[A](m: SubstEnv => A)(implicit s: SessionEnv) = m(new SubstEnv(s.classes))


  def install(v: TermVar, rep: Runtime)(implicit s: SessionEnv) = v.name match {
    case Some(g : Global) =>
       s.env = s.env + (v -> rep)
       s.termNames = s.termNames + (g -> v)
    case _ => die("install: non-global variable: " + v)
  }

  // @throws Death
  def primOp(loc: Loc, name: Global, rep: Runtime, t: Type)(implicit s: SessionEnv, su: Supply): TermVar = {
    val v = V(Loc.builtin, su.fresh, Some(name), Bound, t.nf)
    s.termNames.get(name) match {
      case Some(v) => die("primOp: rebinding " + name)
      case None    =>
        s.env = s.env + (v -> rep)
        s.termNames = s.termNames + (name -> v)
        v
    }
  }
  def primOp(name: Global, rep: Runtime, ty: Type)(implicit s: SessionEnv, su: Supply): TermVar = primOp(Loc.builtin, name, rep, ty)

  def addCon(c: Con)(implicit s: SessionEnv): Con =
    if (s.cons.contains(c.name)) die("addCon: rebinding constructor " + c.name)
    else {
      s.cons = s.cons + (c.name -> c)
      c
    }

  def parse[A](p: Parser[A], ps: ParseState)(implicit su: Supply): (ParseState, A) =
    p.run(ps, su.split) match {
      case Left(err) => die(err.pretty) // TODO: preserve err.stack.reverse.map({case (p,s) => p.report(s).toString}) ++ ("parsing" :: xs))
      case Right(r)  => r
    }

  // @throws Death
  def acyclic(x: SourceFile, xs: List[SourceFile]) = if (xs.exists(_ == x)) {
    val cycle = (x :: (xs.takeWhile(_ != x) ++ List(x))).map(x => text(x.toString)).reverse
    die("error: circular dependency" above nest(2, fillSep(punctuate(" => ", cycle))))
  }

  val depCache = new HashMap[SourceFile, (Long, Dep)] with SynchronizedMap[SourceFile, (Long, Dep)]

  sealed abstract class SourceFile extends scala.Product with Serializable {
    // @throws Death
    def contents: String
    def defaultModuleName: String
    /** Whether loaded from some non-`SourceFile.Loader` source. */
    def exotic: Boolean = false
    def lastModified: Option[Long]
  }

  case class Filesystem(fileName: String, override val exotic: Boolean = false)
      extends SourceFile {
    private val file = new File(fileName)
    def exists = file.exists
    def lastModified = if (exists) Some(file.lastModified) else None
    def contents =
      if(file.exists) {
        val source = scala.io.Source.fromFile(fileName, "UTF-8")
        val str = source.mkString
        source.close
        str
      } else die("File '" + fileName + "' does not exist.")
    def defaultModuleName: String = {
      val path = fileName.split(separatorChar).toList
      val sections = path.filter(s => s.length > 0 && s.head.isUpper) match {
        case List() => path
        case l      => l
      }
      (sections.init ++ List(sections.last.split('.')(0))).mkString(".") // strip off any file extension
    }
    override def toString = fileName
  }

  case class Resource(module: String, url: URL) extends SourceFile {
    def contents = {
      val source = scala.io.Source.fromURL(url, "UTF-8")
      val str = source.mkString
      source.close
      str
    }
    def defaultModuleName: String = module
    def lastModified = Some(0)
    override def toString = url.toString
  }

  case class Literal(contents: String, defaultModuleName: String) extends SourceFile {
    def lastModified = Some(0)
    override def toString = defaultModuleName |+| "<dynamic>"
  }

  case class NotFound(module: String) extends SourceFile {
    def contents = die("Module not found: '" + module + "'")
    def defaultModuleName: String = module
    def lastModified = None
  }

  object SourceFile {
    type ALoader[-A] = A => Option[SourceFile]
    type Loader = ALoader[String]

    /** Search subloaders in order. */
    def inOrder[A](ls: ALoader[A]*): ALoader[A] =
      s => (ls.view map (_(s)) find (_ isDefined) join)

    /** Load from arbitrary filesystem location.
      *
      * @param root Filepath to Ermine module location.
      */
    def filesystem(root: String)(module: String): Option[SourceFile] = {
      val fileName = (root :: hierarchy(module)).mkString(separator) + ".e"
      if (new File(fileName) exists) Some(Filesystem(fileName))
      else None
    }

    /** Load from Java classloader, rooted at `root`. */
    def classloader(root: String = "modules")(module: String): Option[SourceFile] = {
      val path = (root :: hierarchy(module)).mkString("/") + ".e"
      Option(classOf[Resource].getClassLoader.getResource(path)) map {url =>
        if (Option(url.getProtocol) cata ("file".equalsIgnoreCase, false))
          Filesystem(new File(url.toURI.getPath).getPath)
        else Resource(module, url)
      }
    }

    /** Standard module loading rules. */
    def defaultLoader: Loader = classloader()

    private[SourceFile] def hierarchy(module: String): List[String] =
      module.split('.').toList

    private[session] def forModule(module: String)(implicit s: SessionEnv): SourceFile =
      s.loadFile(module) | NotFound(module)

    // evil
    private[Session] def cache(sf: SourceFile, d: Dep): Dep = {
      sf.lastModified foreach (t => depCache += (sf -> (t, d)))
      d
    }

    private[Session] def cached(sf: SourceFile): Option[Dep] = for {
      lmd <- depCache get sf
      (lm, d) = lmd
      newTime <- sf.lastModified
      if newTime == lm
    } yield d

    private def sourceFileTypeScore(sf: SourceFile) = sf match {
      case _: Filesystem => 0
      case _: Resource => 10
      case _: Literal => 20
      case _: NotFound => 30
      // update sourceFileOrdering if you add more here
    }

    implicit def sourceFileOrdering = new Ordering[SourceFile] {
      def compare(x: SourceFile, y: SourceFile) =
        (x, y, sourceFileTypeScore(x) - sourceFileTypeScore(y)) match {
          case (_, _, n) if n /== 0                => n
          case (Filesystem(fn1, e1),  Filesystem(fn2, e2),  _) =>
            Ordering[(String, Boolean)].compare((fn1,e1),(fn2,e2))
          case (Resource(m1, u1), Resource(m2,u2),  _) =>
            Ordering[(String,String)].compare((m1,u1.toString), (m2,u2.toString))
          case (Literal(s1, mn1), Literal(s2, mn2), _) =>
            Ordering[(String,String)].compare((s1, mn1), (s2, mn2))
          case (NotFound(s1),     NotFound(s2),     _) =>
            Ordering[String].compare(s1,s2)
          case (_, _, _) => sys.error("missing case: %s, %s" format (x, y))
      }
    }
  }

  private def cacheDep(file: SourceFile, making: List[SourceFile], expectedName: Option[String])(p: => Dep): Dep = {
    SourceFile.cached(file) match {
      case Some(d) => d copy (making = making, expectedName = expectedName)
      case None    => SourceFile.cache(file, p)
    }
  }

  private val all: (Option[String],List[Explicit],Boolean) = (None, List(), false)

  def dep(file: SourceFile, making: List[SourceFile] = Nil, expectedName: Option[String] = None)(implicit su: Supply): Dep = {
    acyclic(file, making)
    cacheDep(file, file :: making, expectedName) {
      val (ps, mh) = parse(moduleHeader(file.defaultModuleName), ParseState.mk(file.toString, file.contents, file.defaultModuleName))
      val expTys = mh.importExports.flatMap { ie => ie.explicits.collect { case e if e.isType => e.global } }
      val expTms = mh.importExports.flatMap { ie => ie.explicits.collect { case e if !e.isType => e.global } }
      Dep(
        mh.loc,
        file,
        expectedName,
        mh.name,
        mh.importExports.map(_.module).toSet,
        file :: making,
        (s, su) => s.loadedFiles.get(file) match {
          case Some(_) => None // we were already loaded
          case None    => Some(parse(moduleBody(mh), ps.importing(s.termNames, s.cons.keySet, mh.imports))(su))
        },
        expTys,
        expTms
      )
    }
  }

  type ModuleName = String
  type FileName = String

  def depsPrime(
    mods: Set[ModuleName], // loadedModules
    files: Map[SourceFile, ModuleName], // loadedFiles
    tick: Int = 0
  )(ds: List[Dep])(implicit s: SessionEnv, su: Supply): List[Dep] = {
    val m = ds.flatMap(d => d.imports.map((_,d.making))).toMap -- mods
    if (m.isEmpty) Nil
    else {
      val nds = m.toList.map {
        case (mn,making) => fork {
          case (_, sup) => dep(SourceFile.forModule(mn), making, Some(mn))(sup)
        }
      }
      val ndsp = joins(nds)
      ndsp ++ depsPrime(mods, files, tick + 1)(ndsp)
    }
  }

  // @throws Death
  def deps(modules: Set[String])(implicit s: SessionEnv, su: Supply): List[Dep] = {
    val ds = modules.map(m => dep(SourceFile.forModule(m), List(), Some(m))).toList
    ds ++ depsPrime(s.loadedModules, s.loadedFiles)(ds)
  }

  case class Dep(
    loc: Loc,
    file: SourceFile,
    expectedName: Option[String],
    moduleName: String,
    imports: Set[String],
    making: List[SourceFile],
    read: (SessionEnv, Supply) => Option[(ParseState, Module)],
    typeReqs: List[Global],
    termReqs: List[Global]
  ) extends Located {
    def --(xs: Traversable[String]) = copy(imports = imports -- xs)
    // @throws Death
    def make(implicit s: SessionEnv, su: Supply) {
      checkNames
      read(s,su) match {
        case None => ()
        case Some((ps, m)) =>
          loadModule(ps, m)
          s.loadedFiles = s.loadedFiles + (file -> m.name)
          s.loadedModules = s.loadedModules + m.name
      }
    }
    // @throws Death
    def checkNames(implicit s: SessionEnv) {
      for (n <- expectedName)
        if (moduleName != n)
          loc.die("expected a module named " + n)
      for (g <- typeReqs)
        if (!s.cons.contains(g))
          loc.die("Module '" + g.module + "' does not export type '" + g.string + "'.")
      for (g <- termReqs)
        if (!s.termNames.contains(g))
          loc.die("Module '" + g.module + "' does not export term '" + g.string + "'.")
    }
  }

  val percentFmt = new DecimalFormat("##0")
  val secFmt = new DecimalFormat("0.00")

  private def barP(k: Int, n: Int, t0: Long)(implicit con: Printer) =
    if (n == k) say(" " * (n + 13) + "\r")
    else say("[" + ("=" * k) + ("." * (n - k)) + "] " +
      percentFmt.format((k * 100.0) / n) + "% " +
      secFmt.format((nanoTime - t0)/1000000000.0) + "s\r")

  private def bar(k: Int, n: Int, t0: Long)(implicit con: Printer) =
    if (n >= 66) barP(k * 66 / n, 66, t0)
    else if (n >= 0) barP(k,n, t0)

  def loadMore(
    k: Int,
    n: Int,
    t0: Long,
    ds: Map[String, Dep],
    cps: Map[String,Set[String]],
    latches: Map[String, Int],
    zs: Set[String],
    tick: Int = 0
  )(implicit s: SessionEnv, su: Supply, con: Printer): Unit =
    if (zs.isEmpty) bar(n,n,t0)
    else {
      val ((ls, nzs), makes) = mapAccum((latches, Set[String]()), zs.toList) {
        case ((ls,nzs), z) =>
          val a = ds.get(z) match {
            case Some(dsz) =>
               // sayLn("Loading " + z + " in pass " + tick)
               fork { (sp,sup) => dsz.make(sp,sup) }
            case None => die("Can't load " + z)
          }
          ( cps.get(z) match {
              case None => (ls, nzs)
              case Some(ps) => ps.foldLeft((ls,nzs)) {
                case ((ls,nzs),p) =>
                  ls.get(p) match {
                    case Some(lsp) =>
                      if (lsp == 1)   (ls - p, nzs + p)
                      else (ls + (p -> (lsp - 1)), nzs)
                    case None => (ls, nzs)
                  }
              }
          }, a)
      }
      joins(makes)
      val nk = k + makes.length
      bar(nk,n,t0)
      loadMore(nk, n, t0, ds, cps, ls, nzs, tick + 1)
    }

  def loadModules(moduleNames: List[String])(implicit s: SessionEnv, su: Supply, con: Printer): Set[String] = {
    val x = first
    val t0 = nanoTime
    val loaded = s.loadedModules
    val ds = deps(moduleNames.toSet &~ loaded).map(_ -- loaded)
    val needed = ds.map(_.moduleName).toSet &~ loaded
    val n = needed.size
    if (n == 0) Set[String]()
    else {
      info("Loading " + nest(2, oxford("and", needed.toList.sorted.map(text))))
      bar(0,n,t0)
      val cps = ds.foldLeft(Map[String, Set[String]]()) {
        (m,d) => d.imports.foldLeft(m) {
          case (m,c) => m + (c -> (m.getOrElse(c, Set()) + d.moduleName))
        }
      }
      val (zs,nzs) = ds.partition(_.imports.isEmpty)
      val latches = nzs.map(d => d.moduleName -> d.imports.size).toMap
      try {
        loadMore(
          0,
          n,
          t0,
          ds.map(d => d.moduleName -> d).toMap,
          cps,
          latches,
          zs.map(_.moduleName).toSet
        )
      } catch {
        case e: Exception =>
          say("\n")
          throw e
      }
      needed
    }
  }

  def loadModulesInSeries(moduleNames: List[String])(implicit s: SessionEnv, su: Supply, con: Printer) =
    for (m <- moduleNames) load(SourceFile.forModule(m), Some(m))

  def readModule(fileName: String)(implicit s: SessionEnv, su: Supply, con: Printer): Module = {
    val file = Filesystem(fileName)
    val d = dep(file)
    val ms = s.loadedModules
    for (m <- d.imports &~ ms)
      load(SourceFile.forModule(m), Some(m), List(file))
    d.read(s,su).get._2
  }

  // evaluate an expression given by text, in the context of a set of imported modules
  def eval(
    text: String,
    importedModules: Map[String, (Option[String], List[Explicit], Boolean)],
    source: String = "<interactive>"
  )(implicit s: SessionEnv, su: Supply, con: Printer): (Type, Runtime) = {
    loadModules(importedModules.keySet.toList)
    val (eps,a) = parse(phrase(term), ParseState.mk(source,text, "REPL").importing(s.termNames, s.cons.keySet, importedModules))
    val ty = subst { implicit hm => inferType(Nil,a.close) }
    (ty, Term.eval(a, s.env))
  }

  def evalInContext(
    moduleText: String,
    exprText: String,
    source: String = "<remote>"
  ): (SessionEnv, Supply, Printer) => Runtime = (s: SessionEnv, su: Supply, con: Printer) => {
    implicit val is : SessionEnv = s
    implicit val isu : Supply = su
    implicit val icon : Printer = con
    val fileName = "Remote.m" // Remote.e!
    val (psz, h) = parse(moduleHeader("Remote.m"), ParseState.mk(source, moduleText, "Remote"))
    loadModules(h.importExports.map(_.module))
    val snap = s.copy
    val (ps, m) = parse(moduleBody(h), psz.importing(snap.termNames, snap.cons.keySet, h.imports))
    val maps = loadModule(ps, m)
    val (_, tm) = parse(phrase(term), ps copy (loc = Pos.start(fileName, exprText),
                                               offset = 0,
                                               input = exprText))
    val tmp = subTermMaps(maps, tm).close
    val ty = subst { implicit hm => inferType(Nil, tmp) }
    val env = s.env
    s := snap
    Term.eval(tm, env).nf
  }

  // load a module from a file. optionally checking to see if the name is what you expected
  // and/or passing a list of modules we're currently building for circular dependency checking
  // @throws Death
  def load(
    file: SourceFile,
    expectedModuleName: Option[String] = None,
    making: List[SourceFile] = Nil
  )(implicit s: SessionEnv, su: Supply, con: Printer) : String = s.loadedFiles.get(file) match {
    case Some(m) =>
      if (expectedModuleName.isDefined && expectedModuleName.get != m)
        die(file.toString :: ":1:1: error: expected a module named" :+: expectedModuleName.get)
      else m
    case None =>
      val d = dep(file, making)
      if (expectedModuleName.isDefined && expectedModuleName.get != d.moduleName)
        d.die("expected a module named " + expectedModuleName.get)
      for (m <- d.imports &~ s.loadedModules)
        load(SourceFile.forModule(m), Some(m), file :: making)
      d.make
      d.moduleName
  }

  def conMap(mod: String, tn: Map[Name,TypeVar])(implicit s: SessionEnv): Map[TypeVar,Type] =
    Type.conMap(mod, tn, s.cons)

  // @type Death
  def global(m: String, v: V[Any]): Global = v.name match {
    case Some(l : Local)                   => l global m
    case Some(g : Global) if g.module == m => g
    case _                                 => v.die("error: expected local name")
  }

  type Maps = (Map[TypeVar,Type],Map[TermVar,TermVar])

  def emptyMaps: Maps = (Map(),Map())
  def appendMaps(p: Maps, q: Maps): Maps = (p._1 ++ q._1, p._2 ++ q._2)
  def foldMaps(xs: List[Maps]): Maps = xs.foldLeft(emptyMaps)(appendMaps)

  def subTypeMaps[A:HasTypeVars](m: Maps, a: A): A = subType(preserveLoc(m._1), a)
  def subTermMaps[A:HasTermVars](m: Maps, a: A): A = subTermEx(Map(), preserveLoc(m._1), preserveLoc(m._2), a)
  def processTypeDefComponent(mn: String)(maps: Maps, tds: List[TypeDef])(implicit se: SessionEnv, su: Supply): Maps = {
    val dvs = tds.map(_.v)
    val tdsp = subTypeMaps(maps, tds).map(_.closeWith(dvs))
    for (td <- tdsp) assertTypeClosed(td, dvs.toSet)
    val ktds = subst(implicit hm => inferTypeDefKindSchemas(tdsp))
    var conMap: Map[TypeVar,Type] = null
    val cons = ktds.map {
      case (ks, DataStatement(l, v, kindArgs, typeArgs, cons)) =>
        v -> addCon(Con(l, global(mn, v), new ConDecl { def desc = "data" }, ks))
      case (ks, ClassBlock(l, v, kindArgs, typeArgs, ctx, privates, body)) =>
        v -> addCon(Con(l, global(mn, v), ClassDecl, ks))
      case (ks, TypeStatement(l, v, kindArgs, typeArgs, body)) =>
        v -> addCon(Con(l, global(mn, v), new TypeAliasDecl(kindArgs, typeArgs, { subType(preserveLoc(conMap - v), body) }), ks))
    }
    conMap = cons.toMap
    mapAccum_((maps._1 ++ conMap, maps._2), ktds.zip(cons)) {
      case (s, ((_, DataStatement(l, v, kindArgs, typeArgs, cons)), (_, con))) =>
        (s._1, s._2 ++ cons.map {
           case (es, v, fields) => v -> mkDataConstructor(v.loc,  global(mn, v), con.schema.forall, es, typeArgs, con, subTypeMaps(s, fields))
        })
      case (s, ((_, ClassBlock(l,v, kindArgs, typeArgs, ctx, privates, body)), (_, con))) =>
        addClass(l, con, typeArgs, subTypeMaps(s, ctx), _ => typeArgs.map(_ => Bottom(sys.error("hahahahah"))))
        s
      case (s, _) => s
    }
  }

  lazy val first = nanoTime
  def profile(s: String, start: Long, times: (String, Long)*) =  {
    val df = new DecimalFormat("0.0000")
    val (end, msg) = (times.toList.foldLeft((start, s :: ":")) {
      case ((last,s),(msg,n)) =>
        (n, s :+: df.format((n - last) / 1000000000.0) :: "s" :+: "(" :: msg :: text(")"))
    })
    println(
      ((start - first) / 1000000).toString :: "ms" :+: "-" :+:
      ((end - first) / 1000000).toString :: "ms" :+:
      msg :+: df.format((end - start) / 1000000000.0) :: "s (overall)"
    )
  }

  def mkDataConstructor(
    loc: Loc,
    g: Global,
    ks: List[KindVar],
    es: List[TypeVar],
    ts: List[TypeVar],
    con: Type,
    f: List[Type])(implicit s: SessionEnv, su: Supply) =
    primOp(loc, g, Runtime.accumData(g, Nil, f.length),
      Forall.mk(loc.inferred, ks, ts ++ es, Exists(loc.inferred),
        f.foldRight(con(ts.map(VarT(_)):_*))(Arrow(loc.inferred,_,_))))

  // assumes the binding group has had its cons replaced
  def loadModule(ps: ParseState, m: Module)(implicit s: SessionEnv, su: Supply): Maps = {
    val prior = nanoTime
    var maps = (Type.conMap(m.name, ps.typeNames, s.cons), Map(): Map[TermVar,TermVar])
    val mod = m.name
    maps = mapAccum_(maps, m.fields) { processFieldStatement(mod, ps) }
    maps = mapAccum_(maps, m.foreignData) { processForeignDataStatement(mod) }
    maps = mapAccum_(maps, typeDefComponents(m.types)) { processTypeDefComponent(mod) }
    maps = mapAccum_(maps, m.foreigns) {
      (cm, cs) => cs match {
        case ffs : ForeignFunctionStatement    => processForeignFunctionStatement(mod)(cm, ffs)
        case fms : ForeignMethodStatement      => processForeignMethodStatement(mod)(cm, fms)
        case fvs : ForeignValueStatement       => processForeignValueStatement(mod)(cm, fvs)
        case fcs : ForeignConstructorStatement => processForeignConstructorStatement(mod)(cm, fcs)
        case fss : ForeignSubtypeStatement     => processForeignSubtypeStatement(mod)(cm, fss)
      }
    }
    maps = mapAccum_(maps, m.tables) { processTableStatement(mod) }
    val miscStatementTime = nanoTime
    val is = subTermMaps(maps, m.implicits).map(_.close).toList
    val es = subTermMaps(maps, m.explicits).map(_.close).toList
    val bs : List[Binding] = is ++ es
    val env = s.env
    assertTermClosed(bs, env.keySet ++ bs.map(_.v))
    assertTypeClosed(bs)
    val closureTime = nanoTime
    val (_, ds, terms) = subst { implicit hm =>
      val r = inferBindingGroupTypes(m.loc, Nil, is, es, true)
      if (!hm.remembered.isEmpty) {
        println("\nRemembered terms:\n")
        hm.remembered.values.toSeq
          .sortBy(_._3)(Loc.locOrder.toScalaOrdering)
          .foreach { case (_, typ, loc) =>
            println(loc.report(Pretty.prettyType(typ)))
        }
      }
      // do something with hm here, which is a SubstEnv
      r
    }
    for (d <- ds)
      if (!d.isTrivialConstraint)
        d.die("non-trivial top level constraint")
    val bgTime = nanoTime
    val mp = m.subTerm(terms)
    val pts = mp.privateTerms
    val buf = new ListBuffer[(Global,TermVar)]()
    terms.foreach {
      case (k,v) if !pts.contains(v) =>
        val g = global(mp.name, v)
        buf += (g -> v.copy(name = Some(g)))
      case _ => ()
    }
    val tm = buf.toMap
    val substTime = nanoTime

    val exports = m.importExports.filter(_.export)
    // re-exported terms
    val ess = for {
      (k,v) <- s.termNames
      e <- exports.filter(_.module == k.module)
      if e.exported(false, k)
    } yield (k.localized(e.as, Explicit.lookup(k, e.explicits.filter(!_.isType))).global(mp.name), v)

    val tmp = tm ++ ess
    // re-exported type cons
    val etcs = for {
      (k,v) <- s.cons
      e <- exports.filter(_.module == k.module)
      if e.exported(true, k)
    } yield (k.localized(e.as, Explicit.lookup(k, e.explicits.filter(_.isType))).global(mp.name), v)

    val reexportTime = nanoTime

    val tn = s.termNames
    val cs = s.cons

    val overwrites = tmp.keySet.intersect(tn.keySet).toList
    if (!overwrites.isEmpty)
      mp.die("error: loading would overwrite" :+:
        ordinal(overwrites.length,"existing global:", "existing globals:") :+:
        fillSep(punctuate("," :: line, overwrites.toList.map(Pretty.ppName(_).run)))
      )

    val overwrites2 = etcs.keySet.intersect(cs.keySet).toList
    if (!overwrites2.isEmpty)
      mp.die("error: loading would overwrite" :+:
        ordinal(overwrites2.length,"existing type constructor:", "existing type constructors:") :+:
        fillSep(punctuate("," :: line, overwrites2.toList.map(Pretty.ppName(_).run)))
      )

    val overwrites3 = tm.values.toSet.intersect(env.keySet).toList
    if (!overwrites3.isEmpty)
      mp.die("error: loading would overwrite" :+:
        ordinal(overwrites3.length,"existing global", "existing globals") :+: "in the environment:" :+:
        fillSep(punctuate("," :: line, overwrites3.toList.map(Pretty.ppVar(_).run)))
      )

    val overwriteCheckTime = nanoTime

    val gptms = mp.privateTerms.map(global(mp.name, _)).toList
    val gptys = mp.privateTypes.map(global(mp.name, _)).toList

    val mpbs = subTermMaps(maps, (mp.implicits ++ mp.explicits) : List[Binding]).map(_.close)

    var envp: Term.Env = null
    envp = env ++ mpbs.map(b => b.v -> Thunk(Term.evalBinding(b, envp)))

    s.env = envp -- pts
    s.termNames = (tmp ++ s.termNames) -- gptms
    s.cons = (etcs ++ s.cons) -- gptys

    val endTime = nanoTime
    // _ <- profile(mp.name + " loadModule", prior, "misc" -> miscStatementTime, "closure" -> closureTime, "binding" -> bgTime, "rest" -> endTime)
    (maps._1, maps._2 ++ terms)
  }

  def unfurlType: Type => (List[Type], Type) = {
    case AppT(AppT(Arrow(_), a), b) => {
      val (ts, t) = unfurlType(b)
      (a :: ts, t)
    }
    case Forall(_, _, _, _, f) => unfurlType(f)
    case b => (Nil, b)
  }

  def perhapsForeign(post: ImportResult, v: => Any): Runtime = post match {
    case Raw => Prim(v)
    case FF  => Prim(new FFI(v))
    case BOOL => if (v.asInstanceOf[Boolean]) True else False
    case IO  => Data(Global("Builtin", "IO"),
                     Array(Fun((kp: Runtime) =>
                            Fun((kf: Runtime) =>
                              Fun((ke: Runtime) => kf(kp)(ke)(Prim(new FFI(v))))))))
  }

  // Legacy marshalling; doesn't take any type information into account.
  def whnfForeign(a: Runtime, name: String): Any =
    a.whnf match {
      case Prim(p) => p.asInstanceOf[Object]
      case Fun(f) => (v: Any) => whnfForeign(f(Prim(v)), name)
      case Rel(r) => r
      case Arr(arr) if(arr.length == 0) => ()
      case b@Bottom(e) => b.extract[Any]
      case other => other
      // case e => error("Panic: foreign method " + name + " encountered nonscalar: " + e)
    }

  def marshalForeign(t: Type, a: Runtime, name: String): Any = {
    t match {
      case `bool`  => a.whnf match {
        case True  => true
        case False => false
        case _     => die("panic: marshalForeign: expected boolean, found: " + a.toString)
      }
      case _      => whnfForeign(a, name) // default to legacy
    }
  }

  sealed trait ImportResult
  case object Raw extends ImportResult
  case object FF  extends ImportResult
  case object IO  extends ImportResult
  case object BOOL extends ImportResult

  def foreignLift(methName: String,
                  static: Boolean,
                  post: ImportResult,
                  dom: List[Type],
                  method: java.lang.reflect.Method): Runtime = {
      def mk(self: => Any) : Runtime = try {
        import scala.compat.{Platform => Pform}
        import com.clarifi.reporting.Profile
        val f = (args: Array[AnyRef]) => {
          val time = Pform.currentTime
          try {
            method.invoke(self, args:_*)
          } catch {
              case e : java.lang.reflect.InvocationTargetException =>
                val ep = e.getTargetException
                _log.error((if (ep != null) ep else e).getMessage, ep)
                throw new RuntimeException((if (ep != null) ep else e).getMessage, ep)
              case e : Throwable =>
                println(args.mkString(", "))
                _log.error("error invoking foreign function: " + methName, e)
                throw new RuntimeException("error invoking foreign function: " + methName, e)
            }
            finally
            {
              def formatEntryKey(elapsed: Long) =
                methName + " (" + method.getDeclaringClass.getName + ')'
              def formatElapsed(p: (String,Long)) =
                "Invoked in " + p._2 + "ms: " + p._1
              val elapsed = Pform.currentTime - time
              val entry: (String,Long) = formatEntryKey(elapsed) -> elapsed
              Profile.instance+=(entry)

              if(_log.isDebugEnabled) {
                if( elapsed == 0 ) {
                  if(_log.isTraceEnabled)
                    _log.trace(formatElapsed(entry))
                }
                else {
                   _log.debug(formatElapsed(entry))
                }
              }
            }
        }
        val g = (z: List[Any]) =>
                   perhapsForeign(post, f(z.asInstanceOf[List[AnyRef]].reverse.toArray))
        val h = dom.foldRight(g)((t, b) => z => Fun(a => b(marshalForeign(t, a, methName) :: z)))

        h.apply(Nil)
      } catch { case NonFatal(e) => Bottom(throw e) }
      if (static) mk(null) else Fun(x => mk(whnfForeign(x, methName)))
  }

  def processForeignCommon(mod: String,
                           methName: String,
                           v: TermVar,
                           staticClazz: Option[Class[_]],
                           reporter: Located,
                           tyz: Type)(implicit s: SessionEnv, su: Supply): TermVar = {
    val static = staticClazz.isDefined
    val loc = reporter.loc
    val ty = subst(implicit hm => {
      implicit val loc: Located = tyz
      kindCheck(Nil, tyz, Star(tyz.loc.inferred)); substType(tyz)
    })
    assertTypeClosed(ty)
    val (clazz, domain, codomain, post) = unfurlType(ty) match {
      case (d, c) =>
        val (r, p) = c match {
          case AppT(`io`, a)  => (a.foreignLookup, IO)
          case AppT(`ffi`, a) => (a.foreignLookup, FF)
          case `bool`         => (implicitly[ClassTag[Boolean]].runtimeClass, BOOL)
          case _              => (c.foreignLookup, Raw)
        }
        staticClazz match {
          case Some(clazz) => (clazz, d, r, p)
          case None        => (d.head.foreignLookup, d.tail, r, p)
        }
    }
    val classDomain = domain.map(_.foreignLookup)
    val method = try {
      clazz.getMethod(methName, classDomain:_*)
    } catch {
      case e : Exception =>
        throw Death(
          "method" :+: methName :+:
          "with domain" :+: classDomain.mkString(",") :+:
          "not found in class" :+: text(clazz.getName),
          e
        )
    }

    if (!codomain.isAssignableFrom(method.getReturnType))
      reporter.die(
        "expected return type" :+: codomain.getName :+:
        "does not match foreign return type" :+: text(method.getReturnType.toString)
      )

    if(java.lang.reflect.Modifier.isStatic(method.getModifiers) != static)
      reporter.die(
        "method" :+: methName :+:
        "in class" :+: clazz.getName :+:
        text(if (static) "is not static; use foreign method instead"
             else "is static; use foreign function instead")
      )
    primOp(loc, global(mod, v), foreignLift(methName, static, post, domain, method), ty)
  }

  def processForeignValueStatement(
    mod: String
  )(
    cm: Maps,
    fvs: ForeignValueStatement
  )(implicit s: SessionEnv, su: Supply) = fvs match {
    case ForeignValueStatement(loc, v, ty, ForeignClass(_, clazz), ForeignMember(_, valName)) =>
      var typ = subTypeMaps(cm, ty).close
      val post = typ match {
        case AppT(`ffi`, _) => FF
        case AppT(`io`,  _) => IO
        case `bool`         => BOOL
        case _              => Raw
      }
      typ = subst { implicit hm => {
        implicit val loc: Located = typ
        kindCheck(Nil, typ, Star(typ.loc.inferred)); substType(typ)
      } }
      assertTypeClosed(typ)
      val value = try {
        clazz.getField(valName)
      } catch { case e : Exception =>
          throw Death(loc.report(
            "static field" :+: valName :+:
            "not found in class" :+: text(clazz.getName)
          ), e)
      }
      val r = primOp(
        loc,
        global(mod, v),
        perhapsForeign(post, try { value.get(null) } catch { case NonFatal(e) => throw e.getCause }),
        typ
      )
      (cm._1, cm._2 + (fvs.v -> r))
  }

  def processForeignConstructorStatement(
    mod: String
  )(
    cm: Maps,
    fcs: ForeignConstructorStatement
  )(implicit s: SessionEnv, su: Supply) = fcs match {
    case ForeignConstructorStatement(loc, v, tyz) =>
      var ty = subTypeMaps(cm, tyz).close
      ty = subst { implicit hm => {
        implicit val loc: Located = tyz
        kindCheck(Nil, ty, Star(ty.loc.inferred)); substType(ty)
      } }
      assertTypeClosed(ty)
      val (domain, codomain, post) = unfurlType(ty) match {
        case (d, AppT(`io`,  a)) => (d, a.foreignLookup, IO)
        case (d, AppT(`ffi`, a)) => (d, a.foreignLookup, FF)
        case (d, `bool`)         => (d, implicitly[ClassTag[Boolean]].runtimeClass, BOOL)
        case (d, c             ) => (d, c.foreignLookup, Raw)
      }
      val classDomain = domain.map(_.foreignLookup)
      val ctor = try {
        codomain.getConstructor(classDomain:_*)
      } catch { case e : Exception =>
        throw Death(loc.report(
          "constructor not found for" :+: codomain.getName + "with arguments (" ::
          classDomain.map(_.getName).mkString(", ") :: text(")")
        ), e)
      }
      val name = global(mod, v)
      val g = (args : List[AnyRef]) =>
                perhapsForeign(post,
                  try {
                    ctor.newInstance(args:_*)
                  } catch { case NonFatal(e) => throw e.getCause }
                )
      val f = domain.foldRight((z: List[Any]) => g(z.asInstanceOf[List[AnyRef]].reverse)) { (t, b) =>
                z => Fun(a => b(marshalForeign(t, a, name.string) :: z))
              }
      val r = primOp(loc, name, f.apply(Nil), ty)
      (cm._1, cm._2 + (fcs.v -> r))
  }

  // @throws Death
  def toHeader(mod: String, t: Type)(implicit s: SessionEnv): Header = t match {
    case AppT(_, r) => toHeader(mod, r)
    case ConcreteRho(loc, fields) =>
      fields.map({
        case l : Local  => s.cons(l.global(mod))
        case g : Global => s.cons(g)
      }).map({
        case Con(loc, g, FieldConDecl(Nullable(Con(_, ty, _, _))), _) =>
          g.string -> PrimT.withName(ty.string).withNull
        case Con(loc, g, FieldConDecl(Con(_, ty, _, _)), _) =>
          g.string -> PrimT.withName(ty.string)
        case f => die(f.report("Invalid field in table:" :+: text(f.toString)))
      }).toMap
    case _ => die(t.report("Expected concrete row but found:" :+: text(t.toString)))
  }

  def processTableStatement(mod: String)(cm: Maps, ts: TableStatement)(implicit se: SessionEnv, su: Supply): Maps = ts match {
    case TableStatement(loc, db, vs, tyz) =>
      var ty = subTypeMaps(cm, tyz)
      ty = subst { implicit hm => {
        implicit val loc: Located = ty
        kindCheck(List(), ty, Star(ty.loc.inferred)); substType(ty)(hm)
      } }
      assertTypeClosed(ty)
      mapAccum_(cm, vs) {
        case (cs, ns ++ v) =>
          val u = primOp(global(mod, v),
                         Rel(ExtRel(Table(toHeader(mod, ty),
                                               TableName(v.name.get.string,
                                                         ns.map(_.string))), db)), ty)
          (cs._1, cs._2 + (v -> u))
      }
  }

  // deliberately does not take the con map, we don't need it
  def processForeignDataStatement(mod: String)(cm: Maps, fds: ForeignDataStatement)(implicit s: SessionEnv, su: Supply): Maps = fds match {
    case ForeignDataStatement(loc, v, vs, clazz) =>
      val k = vs.foldRight(Star(loc.inferred) : Kind)((u, r) => ArrowK(loc.inferred, u.extract, r))
      val c = addCon(Con(loc, global(mod, v), TypeConDecl(clazz.cls, true), k.schema))
      (cm._1 + (v -> c), cm._2)
  }

  def processForeignSubtypeStatement(mod: String)(cm: Maps, fss: ForeignSubtypeStatement)(implicit s: SessionEnv, su: Supply): Maps = {
    var ty = subTypeMaps(cm, fss.ty).close
    ty = subst { implicit hm => {
      implicit val loc: Located = fss.ty
      kindCheck(Nil, fss.ty, Star(fss.loc.inferred)); substType(ty)
    } }
    assertTypeClosed(ty)
    (cm._1, cm._2 + (fss.v -> primOp(fss.loc, global(mod, fss.v), Fun(x => x), ty)))
  }

  def processForeignFunctionStatement(mod: String)(cm: Maps, ffs: ForeignFunctionStatement)(implicit s: SessionEnv, su: Supply) =
    ( cm._1,
      cm._2 + (
        ffs.v -> processForeignCommon(mod, ffs.member.name, ffs.v, Some(ffs.cls.cls), ffs.loc, subTypeMaps(cm, ffs.ty).close)
      )
    )

  def processForeignMethodStatement(mod: String)(cm: Maps, fms: ForeignMethodStatement)(implicit s: SessionEnv, su: Supply) =
    ( cm._1,
      cm._2 + (
        fms.v -> processForeignCommon(mod, fms.member.name, fms.v, None, fms.loc, subTypeMaps(cm, fms.ty).close)
      )
    )

  /*
   * Expects that the FieldStatement has been 'type checked' and processed
   * such that:
   *
   *   the variables are globalized and have their appropriate unique id
   *   the type is a valid prim type
   *
   * tmv should take the variable names to the term variables that were chosen
   * during checking.
   */
  // @throws Death
  def loadFieldStatement(fs: FieldStatement, tmv: Name => TermVar)(implicit s: SessionEnv, su: Supply) {
    val ty = fs.ty
    val ptyp = ty match {
      case Nullable(typ) => primTypes(typ).withNull
      case _ => primTypes(ty)
    }
    for (v <- fs.vs)
      v.name match {
        case Some(g : Global) =>
          addCon(Con(v.loc.inferred, g, FieldConDecl(ty), Field(v.loc.inferred).schema))
          install(tmv(v.name.get), Data(g, Array(Prim(ptyp))))
        case _ => die("loadFieldStatement: un-globalized variable: " + v)
      }
  }

  def processFieldStatement(module: String, ps: ParseState)(cm: Maps, fs: FieldStatement)(implicit s: SessionEnv, su: Supply) =
    fs.vs.map({ case v =>
      val ty = subTypeMaps(cm, fs.ty)
      val otyp = ty match {
        case Nullable(typ) => primTypes.get(typ) map (_.withNull)
        case _ => primTypes.get(ty)
      }
      if (!otyp.isDefined) die(text("Invalid field type:") :+: text(ty.toString))
      val tyCon = addCon(Con(v.loc.inferred,global(module, v),FieldConDecl(ty),Field(v.loc.inferred).schema))
      val tmv = primOp(fs.loc, tyCon.name, Data(tyCon.name, Array(Prim(otyp.get))),
                       field(ConcreteRho(v.loc.inferred, Set(tyCon.name)), ty))
      ps.termNames.get(v.name.get) match {
        case None    => (Map(v -> tyCon), Map():Map[TermVar,TermVar])
        case Some(u) => (Map(v -> tyCon), Map(u -> tmv))
      }
    }).foldLeft(cm)(appendMaps)

  def addClass(
    l: Loc,
    cls: Con,
    args: List[TypeVar],
    sups: List[Type],
    destroy: Runtime => List[Runtime]
  )(implicit s: SessionEnv): Con = {
    s.classes = s.classes + (cls.name -> ClassDef(l, cls.name, args, sups, destroy, Map()))
    def step(c: Con): List[Con] = s.classes.get(c.name) match {
      case None => List()
      case Some(cls) => cls.sups.flatMap(unfurlApp(_) match {
        case Some((cp,_)) => List(cp)
        case None => List()
      })
    }
    def go(c: Con) {
      for (cp <- step(c))
        if (cp.name == cls.name) c.die("cyclic class hierarchy")
        else go(cp)
    }
    go(cls)
    cls
  }

  def unsafePerformSession[A](m: (SessionEnv, Supply, Printer) => A): A = {
    implicit val con = Printer.simple
    implicit val s = new SessionEnv
    implicit val su: Supply = Supply.create
    val lib = Lib.preamble
    m(s,su,con)
    // try { m } catch { case Death(err, _) => sys.error("Failure:\n" + err) }
  }

  def parseModule(filename: String, content: String, module: String)(implicit s: SessionEnv, v: Supply): Either[Err, Module] =
    moduleHeader(module).run(ParseState.mk(filename, content, module), v).right flatMap {
      case (ps, mh) => moduleBody(mh).run(ps.importing(s.termNames, s.cons.keySet, mh.imports), v).
                                      right.map(_._2)
    }
}
