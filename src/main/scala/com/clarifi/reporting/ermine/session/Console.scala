package com.clarifi.reporting
package ermine
package session

import scala.io.{ Source }

import jline.{ ConsoleReader, Terminal, SimpleCompletor, ArgumentCompletor, MultiCompletor, FileNameCompletor }
import java.awt.Toolkit
import java.awt.datatransfer.{Clipboard, DataFlavor}

import java.util.Date
import java.io.{ PrintWriter, InputStream, FileInputStream, FileDescriptor, OutputStreamWriter }
import java.io.File.separator
import java.lang.Exception
import scala.collection.immutable.List
import scalaz.Monad
import scalaz.Scalaz._

import com.clarifi.reporting.ermine.parsing.{
  phrase, semi, eof,
  startingKeywords, otherKeywords,
  Parser, ParseState,
  TermParsers, StatementParsers,
  ModuleHeader, ModuleParsers
}

import com.clarifi.reporting.ermine.parsing.TermParsers.term
import com.clarifi.reporting.ermine.parsing.TypeParsers.typ
import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Document._
import com.clarifi.reporting.ermine.Pretty.{
  prettyRuntime, prettyType, prettyKind, prettyVarHasType, prettyVarHasKind, prettyTypeHasKindSchema, prettyConHasKindSchema
}
import com.clarifi.reporting.ermine.Type.typeVars
import com.clarifi.reporting.ermine.Term.{ eval, termVars }
import com.clarifi.reporting.ermine.Subst.{ inferType, inferKind }
import com.clarifi.reporting.ermine.session.Session.{
  load, loadModule, loadModules, primOp, SourceFile, Filesystem, loadModulesInSeries, subst
}
import com.clarifi.reporting.ermine.session.Printer.{ benchmark, sayLn }
import syntax.{Renaming, Explicit, Statement, ImportExportStatement, ImportExportCommand, ModuleCommand, ExpressionCommand, EmptyCommand}

case class Mark(currentResult: Int, imports: Map[String, (Option[String],List[Explicit],Boolean)], sessionEnv: SessionEnv)

case class ConsoleException(msg: Option[Document] = None) extends Exception(msg.getOrElse(text("error")).toString)

abstract class Action(val name: String, val alts: List[String], arg: Option[Document], desc: Document) {
  def apply(s: String)(implicit e: ConsoleEnv): Unit
  private def argDoc = arg match {
    case Some(n) => space :: n
    case None => empty
  }
  def doc = text("    " + name) :: argDoc :: column(n => (" " * (30 - n)) :: nest(2, desc))
  def matches(s: String) = name.startsWith(s) || alts.exists(_ startsWith s)
}

class ConsoleEnv(
  _sessionEnv: SessionEnv,
  val in: InputStream = new FileInputStream(FileDescriptor.in),
  val out: PrintWriter = new PrintWriter(new OutputStreamWriter(System.out)),
  val terminal: Terminal = Terminal.getTerminal
) {
  implicit val supply: Supply = Supply.create
  implicit val con = new Printer {
    def apply(s: String) {
      reader.printString(s)
      out.flush
    }
  }

  // can't make this a val without losing sessionEnv = syntax. also, functions that take this often throw exceptions
  // so use the session(implicit s => ...) combinator instead
  def sessionEnv: SessionEnv = _sessionEnv

  var quit: Boolean = false
  var helpHinted: Boolean = false
  def helpHint {
    if (!helpHinted) {
      sayLn("Use \":help\" to see a list of commands")
      helpHinted = true
    }
  }

  // mark/release
  var marks: List[Mark] = List()
  def sayLnMarks {
    val n = marks.length
    sayLn(Ordinal(n, "entry", "entries") :+: text("in the mark stack."))
  }
  var namedMarks: Map[String, Mark] = Map()

  var currentResult: Int = 0

  def mark = Mark(currentResult, imports, sessionEnv.copy)
  def mark_=(m: Mark) {
    currentResult = m.currentResult
    imports = m.imports
    sessionEnv_=(m.sessionEnv)
  }

  // repl and autocomplete
  val reader = new ConsoleReader(in, out, null, terminal)

  // auto-completor (sic)
  val completor = new SimpleCompletor("")
  completor.setDelimiter(" ")

  val loadCompletor = new ArgumentCompletor(List(
    new SimpleCompletor(":load"),
    new FileNameCompletor
  ).toArray)
  loadCompletor.setStrict(true)

  val argCompletor = new ArgumentCompletor(
    List(
      new MultiCompletor(
        List(
          new SimpleCompletor((Console.actions.flatMap(a => a.name :: a.alts) ++ startingKeywords).toArray),
          completor
        ).toArray : Array[jline.Completor]
      ),
      completor
    ).toArray
  )
  argCompletor.setStrict(false)

  reader.addCompletor(
    new MultiCompletor(
      List(
        loadCompletor,
        argCompletor
      ).toArray : Array[jline.Completor]
    )
  )

  var imports: Map[String, (Option[String],List[Explicit],Boolean)] = Map() // module -> affix

  def asImported(g: Name): Name = g match {
    case g : Global => imports.get(g.module) match {
      case Some((as,explicits,_)) => g.localized(as, Explicit.lookup(g, explicits))
      case None => g
    }
    case _ => g
  }

  def updateCompletor {
    val ps = parseState("")
    val names = otherKeywords ++ (ps.termNames.keySet ++ ps.typeNames.keySet ++ ps.kindNames.keySet).map(_.string)
    completor.setCandidateStrings(names.toArray)
  }

  def assumeClosed(t: Term)(doIt: => Unit) {
    val env = sessionEnv.env
    val undefinedTerms = (termVars(t) -- env.keySet).toList
    val undefinedTypes = typeVars(t).toList
    if (undefinedTerms.isEmpty && undefinedTypes.isEmpty) doIt
    else {
      sayLn(vsep(undefinedTerms.map(v => v.report("error: undefined term"))))
      sayLn(vsep(undefinedTypes.map(v => v.report("error: undefined type"))))
    }

  }

  def eval(t: Term)(k: Runtime => Unit) {
    assumeClosed(t) {
      Term.eval(t, sessionEnv.env) match {
        case b : Bottom => b.inspect
        case e => k(e)
      }
    }
  }

  def importing(m: String, affix: Option[String], exp: List[Explicit], using: Boolean) { imports = imports + (m -> (affix, exp, using)) }

  updateCompletor

  def sessionEnv_=(s: SessionEnv) {
    sessionEnv := s
    updateCompletor
  }

  def parseState(s: String) = ParseState.mk("<interactive>", s, "REPL").importing(sessionEnv.termNames, sessionEnv.cons.keySet, imports)


  def session[A](s: SessionEnv => A): Option[A] = {
    val envp = sessionEnv.copy
    try {
      val r = s(sessionEnv)
      updateCompletor
      Some(r)
    } catch { case e@Death(err, _) =>
      sessionEnv = envp
      sayLn(err)
      stackHint
      stackHandler = () => sayLn(e.getStackTrace.mkString("\n"))
      None
    }
  }

  def subst[A](s: SubstEnv => A): Option[A] = session(implicit hm => Session.subst(s))

  var stackHinted: Boolean = false
  def stackHint {
    if (!stackHinted) {
      sayLn("Use \":stack\" to see a stack trace")
      stackHinted = true
    }
  }

  val ok = () => sayLn("OK")
  var stackHandler: () => Unit = ok

  def handling(a: => Unit) = try a catch {
    case e : DocException =>
      sayLn("runtime error:")
      sayLn(e.doc)
      stackHint
      stackHandler = () => e.printStackTrace(out)
    case e : Throwable =>
      sayLn("runtime error: " + e.getMessage)
      stackHint
      stackHandler = () => e.printStackTrace(out)
  }

  // if we have a bottom, we want to set the stackHandler
  def handlingBot(a: Throwable) = {
    stackHint
    stackHandler = () => a.printStackTrace(out)
  }

  def conMap(ps: ParseState) = Type.conMap("REPL", ps.typeNames, sessionEnv.cons)

  def fixCons[A](ps: ParseState, a: A)(implicit A: HasTypeVars[A]) =
    Type.subType(conMap(ps), a)
}

object Console {
  def writeLn(s: Document)(implicit e: ConsoleEnv) = sayLn(s)(e.con)
  def mark(implicit e: ConsoleEnv) = e.mark
  def session[A](s: SessionEnv => A)(implicit e: ConsoleEnv): Option[A] = e.session(s)
  def importing(m: String, affix: Option[String] = None)(implicit e: ConsoleEnv) = e.importing(m, affix, List(), false)
  def sessionEnv(implicit e: ConsoleEnv) = e.sessionEnv

  val header = """
    Commands available from the prompt:

    <expr>                    evaluate <expr>
    <statement>               evaluate <statement>"""

  val help = new Action(":help", List("help",":?"), None, "print this message") {
    def apply(s: String)(implicit e: ConsoleEnv) {
      writeLn(text(header) above vsep(actions.map(_.doc)))
    }
  }

  val actions: List[Action] = List(
    new Action(":help", List("help",":?"), None, "print this message") {
      def apply(s: String)(implicit e: ConsoleEnv) { writeLn(text(header) above vsep(actions.map(_.doc))) }
    },
    new Action(":paste", List(), None, "Parse Ermine statements or expressions from the clipboard") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        val clipboard = Toolkit.getDefaultToolkit.getSystemClipboard
        val content = clipboard.getData(DataFlavor.stringFlavor)
        val str = content.toString
        writeLn(str)
        other(str)
      }
    },
    new Action(":quit", List("quit"), None, "end this session") {
      def apply(s: String)(implicit e: ConsoleEnv) { e.quit = true }
    },
    new Action(":stack", List(), None, "print the stack trace of the last error") {
      def apply(s: String)(implicit e: ConsoleEnv) { e.stackHandler() }
    },
    new Action(":crash",List(),None,"crash") {
      def apply(s: String)(implicit e: ConsoleEnv) { 1/0; () }
    },
    new Action(":slowload",List(),None, "reload all of the modules for the current session (slowly and incorrectly)") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        import e.{con,supply}
        val prior = new Date()
        val old = e.mark
        val files = old.sessionEnv.loadedFiles
        e.mark = e.namedMarks("lib")
        val ok = e.session(implicit s => loadModules(files.values.toList)).isDefined
        if (!ok) {
          e.mark = old
          writeLn("Error during reload, reverting.")
        } else {
          val now = new Date()
          val secs = (now.getTime() - prior.getTime()) / 1000.0
          e.imports = old.imports
          writeLn("Reloaded" :+: ordinal(files.toList.length, "module","modules") :+: "successfully in" :+: secs.toString :+: text("seconds."))
        }
      }
    },
    new Action(":slowerload",List(),None, "reload all of the modules for the current session (slowly and incorrectly)") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        import e.{con,supply}
        val prior = new Date()
        val old = e.mark
        val files = old.sessionEnv.loadedFiles
        e.mark = e.namedMarks("lib")
        val ok = e.session(implicit s => loadModulesInSeries(files.values.toList)).isDefined
        if (!ok) {
          e.mark = old
          writeLn("Error during reload, reverting.")
        } else {
          val now = new Date()
          val secs = (now.getTime() - prior.getTime()) / 1000.0
          e.imports = old.imports
          writeLn("Reloaded" :+: ordinal(files.toList.length, "module","modules") :+: "successfully in" :+: secs.toString :+: text("seconds."))
        }
      }
    },
    new Action(":reload",List(),None, "reload all of the modules for the current session (intelligently)") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        val prior = new Date();
        val old = e.mark
        val lib = e.namedMarks("lib")
        val dcl = Session.depCache.toList
        val dcm = dcl.map({ case (k,(_,v)) => (k,v)}).toMap // a local immutable depCache map sans times
        val possible = dcm.keySet
        // compute transitively dirty modules
        def go(dirt: Set[SourceFile]): Set[SourceFile] = {
          val dm = dirt.map(fn => dcm(fn).moduleName)
          val xs = (possible &~ dirt).filter(p => ! (dcm(p).imports & dm).isEmpty)
          if (xs.isEmpty) dirt
          else go(dirt | xs)
        }
        // a set of filesystem SourceFiles
        val dirtyFiles = go(
          dcl.collect{case (sf, (lm, d))
                      if sf.lastModified map (lm !=) getOrElse true =>
                        sf}.toSet)

        val dirtyModules = dirtyFiles.map(fn => dcm(fn).moduleName)
        val scrubbing = dirtyModules + "REPL"

        val (manualDirtyFiles, simpleDirtyFiles) = dirtyFiles partition (_.exotic)
        val simpleDirtyModules = simpleDirtyFiles.map(fn => dcm(fn).moduleName)

        // scrub those modules back down to their lib state
        val oldState = old.sessionEnv.copy
        val libState = lib.sessionEnv.copy
        sessionEnv.env = oldState.env.filter {
          case (v@V(_,_,Some(Global(m,_,_)),_,_),_) => !scrubbing(m) || libState.env.contains(v)
          case _ => true
        }
        sessionEnv.termNames = oldState.termNames.filter {
          case (n@Global(m,_,_),_) => !scrubbing(m) || libState.termNames.contains(n)
        }
        sessionEnv.cons = oldState.cons.filter {
          case (n@Global(m,_,_),_) => !scrubbing(m) || libState.cons.contains(n)
        }
        sessionEnv.loadedFiles = oldState.loadedFiles.filter { case (k,v) => !scrubbing(v) }
        sessionEnv.loadedModules = oldState.loadedModules &~ scrubbing
        e.currentResult = 0
        val ok = if (simpleDirtyModules.isEmpty && manualDirtyFiles.isEmpty) {
          writeLn("No modules have changed.")
          true
        } else {
          import e.{con,supply}
          session(implicit s =>
            benchmark({
              if (!simpleDirtyModules.isEmpty)
                loadModules(simpleDirtyModules.toList)
              for (fn <- manualDirtyFiles)
                load(fn, Some(dcm(fn).moduleName))
            }) { _ =>
              "Reloaded" :+: ordinal(dirtyModules.size,"dirty module","dirty modules") :+:
              "(" :: ordinal(manualDirtyFiles.size,"exotic file","exotic files") ::
              ") while retaining" :+: ordinal((possible &~ dirtyFiles).size,"module","modules")
            }
          ).isDefined
        }
        if (!ok) {
          e.mark = old
          writeLn("Error during reload, reverting.")
        }
      }
    },
    new Action(":mark",List(),Some("[key]"),"save the current session state for later release") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        val m = e.mark
        e.marks = m :: e.marks
        if (!s.isEmpty) {
          e.namedMarks = e.namedMarks + (s -> m)
          writeLn("Named mark created: " + s)
        }
        e.sayLnMarks
      }
    },
    new Action(":history",List(), None, "show the list of named marks") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        e.sayLnMarks
        e.namedMarks.keySet.toList match {
          case List() => writeLn("No named marks")
          case marks => writeLn("Named marks:" :+: nest(2, fillSep(punctuate(",", marks.map(text(_))))))
        }
      }
    },
    new Action(":release", List(), Some("[key]"), "restore to a given session state") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        if (s.isEmpty) e.marks match {
          case List() => writeLn("No marks!")
          case List(a) => e.mark = a
          case a :: as => e.mark = a
                          e.marks = as
                          e.sayLnMarks
        }
        else e.namedMarks.get(s) match {
          case Some(a) => e.mark = a
          case None    => writeLn("No such mark")
        }
      }
    },
    new Action(":load", List(), Some("<filename>"), "Load a module from a source file") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        import e.{con,supply}
        benchmark(session(implicit se => load(Filesystem(s, exotic=true)))) {
          case Some(n) =>
            importing(n)
            "Importing module '" + n + "'"
          case None    => "Unable to load module"
        }
      }
    },

    // parse and load
    new Action(":parse", List(), Some("<expr>"), "Parse and pretty print an expression") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        phrase(TermParsers.term).run(e.parseState(s), e.supply) match {
          case Left(err)      => writeLn(err.pretty)
          case Right((ps, a)) => writeLn(e.fixCons(ps, a).toString)
        }
      }
    },
    new Action(":eval", List(), Some("<expr>"), "Evaluate an expression") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        phrase(TermParsers.term).run(e.parseState(s), e.supply) match {
          case Left(err)     => writeLn(err.pretty)
          case Right((_, a)) => e.eval(a) { r => writeLn(prettyRuntime(r)) }
        }
      }
    },
    new Action(":imports", List(), None, "Summarize the currently imports") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        val modules = e.imports.toList.sortWith((p,q) => p._1 < q._1).map({
          case (k,(None,_,_))    => text(k)
          case (k,(Some(a),_,_)) => text(k) :+: "as" :+: text(a)
        }).toList
        writeLn("Imports:" :+: nest(2, fillSep(punctuate(",", modules))))
        writeLn("Files:" :+: nest(2, fillSep(punctuate(",",
           e.sessionEnv.loadedFiles.toList.sorted.map({
             case (k,v) => text(k.toString) :+: "=>" :+: text(v)
           }))))
        )
        writeLn("Modules:" :+: nest(2, fillSep(punctuate(",", e.sessionEnv.loadedModules.toList.sorted.map(text(_))))))
      }
    },
    new Action(":source", List(), Some("<module>"), "Show a module's Ermine source code") {
      def apply(s: String)(implicit e: ConsoleEnv) =
        writeLn(e.sessionEnv.loadedFiles.find(_._2 == s)
                map {case (mod, _) =>
                  val rawlines = ("""\r\n|\r|\n""".r split mod.contents view)
                  val lines =
                    if (rawlines.last isEmpty) rawlines.init else rawlines
                  val numwidth = lines.size.toString.size
                  "Contents of" :+: mod.toString :: text(":") above
                     vsep(lines.zipWithIndex map {case (line, n) =>
                       val sn = (n+1).toString
                       (" " * (numwidth - sn.size)) :: sn :: "  " :: text(line)} toStream)}
                getOrElse ("No module for" :+: s :: "."))
    },
    new Action(":groups", List(), Some("<module>"), "Show the binding groups for a module") {
      def apply(s: String)(implicit e: ConsoleEnv) = {
        // HACK: strip out term names for this module if it's already loaded, otherwise
        // get errors
        val e2Env = e.sessionEnv.copy
        e2Env.termNames = e.sessionEnv.termNames.filterKeys(g => g.module != s)
        e2Env.loadedFiles.find(_._2 == s) map { case (mod, modName) =>
          Session.parseModule(modName, mod.contents, modName)(e.sessionEnv, e.supply) match {
            case Left(err) => writeLn(err.toString)
            case Right(m) => writeLn {
              ImplicitBinding.implicitBindingComponents(
                m.implicits ++ m.explicits.map(_ forgetSignature)
              ).map(bs => bs.map(_.v.name.get.string).mkString(", ")).mkString("\n\n")
            }
          }
        }
      }
    },
    new Action(":clear", List(), None, "Clear the screen") {
      def apply(s: String)(implicit e: ConsoleEnv) =
        if (!e.reader.clearScreen())
          writeLn("\n"*e.terminal.getTerminalHeight) // can't clear the screen? come on
    },
    new Action(":type", List(), Some("<expr>"), "Infer the type of an expression") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        phrase(term).run(e.parseState(s), e.supply) match {
          case Left(err)       => writeLn(err.pretty)
          case Right((ps, tm)) =>
            val tmp = e.fixCons(ps, tm).close(e.supply)
            e.assumeClosed(tmp) {
              import e.supply
              e.subst(implicit hm => inferType(List(), tmp, true)) match {
                case Some(ty) =>
                  val ftvs = Type.typeVars(tmp).toList
                  if (ftvs.isEmpty) writeLn(prettyType(ty, -1))
                  else for (v <- ftvs) writeLn(v.report("unresolved type variable"))
                case None     => ()
              }
            }
        }
      }
    },
    new Action(":uglytype", List(), Some("<expr>"), "Infer the type of an expression, dumping the raw syntax") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        phrase(term).run(e.parseState(s), e.supply) match {
          case Left(err)       => writeLn(err.pretty)
          case Right((ps, tm)) =>
            import e.supply
            e.subst(implicit hm => inferType(List(), e.fixCons(ps, tm), true)) match {
              case Some(ty) => writeLn(ty.toString)
              case None     => ()
            }
        }
      }
    },
    new Action(":browse", List(), Some("[substring]"), "Show the types of all known terms (optionally filtered)") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        val ps = e.parseState("")
        val (types, terms) = describeEnvironment(ps, e.sessionEnv, s)
        def render(ts: Iterable[(Local, (Option[String], Document))]) =
          ((ts groupBy (_._2._1)
            mapValues (_.toSeq sortBy (_._1.string))).toSeq sortBy (_._1)
           foreach {case (mod, bindings) =>
             writeLn(mod map ("-- imported via" :+: _)
                     getOrElse text("-- defined in current module"))
             bindings foreach (p => writeLn(p._2._2))
          })
        render(types)
        render(terms)
      }
    },
    new Action(":kind", List(), Some("<type>"), "Infer the kind of a type") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        phrase(typ).run(e.parseState(s), e.supply) match {
          case Left(err)       => writeLn(err.pretty)
          case Right((ps, ty)) =>
            val fty = e.fixCons(ps, ty).close(e.supply)
            val danglingTypes = typeVars(fty).toList
            if (danglingTypes.isEmpty) {
              import e.supply
              e.subst(implicit hm => inferKind(List(), fty)) match {
                case Some(ki) => writeLn(prettyTypeHasKindSchema(fty, ki))
                case None     => ()
              }
            } else {
              danglingTypes.foreach(t => writeLn(t.report("error: undefined type")))
            }
        }
      }
    },
    new Action(":echo", List(), None, "Toggle character echo (for compatibility with some terminals)") {
      def apply(s: String)(implicit e: ConsoleEnv) {
        if (e.reader.getEchoCharacter != null) {
          e.reader.setEchoCharacter(null)
          writeLn("Echo is on")
        }
        else {
          e.reader.setEchoCharacter(new java.lang.Character(0))
          writeLn("Echo is off")
        }
      }
    }
  )

  /** Browse available types and terms prettily. */
  private def describeEnvironment(ps: ParseState, ss: SessionEnv,
                                  filt: String):
                              (Map[Local, (Option[String], Document)],
                               Map[Local, (Option[String], Document)]) = {
    val types = for {
      (tn,cn : Global) <- ps.canonicalTypes.filter(_._1.string.contains(filt))
      c <- ss.cons.get(cn).toList
    } yield ss.classes.get(c.name) match {
      case Some(cls) => (tn, Some(cn.module) -> cls.pretty)
      case None =>      (tn, Some(cn.module) -> (c.decl.desc :+: prettyConHasKindSchema(tn, c.schema)))
    }
    val terms = for {
      (tn,cn) <- ps.canonicalTerms.filter(_._1.string.contains(filt))
      mod = cn match {
        case Global(m, _, _) => Some(m)
        case _: Local => None
      }
      v <- ps.termNames.get(cn).toList
    } yield (tn, mod -> prettyVarHasType(v copy (name = Some(tn))))
    (types, terms)
  }

  def marked(s: String)(implicit e: ConsoleEnv) {
    e.namedMarks = e.namedMarks + (s -> e.mark)
  }

  def pushMark(implicit e: ConsoleEnv) {
    e.marks = e.mark :: e.marks
  }

  sealed trait Balance
  case object Balanced extends Balance
  case object Unbalanced extends Balance
  case object Borked extends Balance

  def balanced(s: String, stk: List[Char] = List()): Balance =
    if (s.length == 0) if (stk.isEmpty) Balanced else Unbalanced
    else s.head match {
      case c@('('|'['|'{') => balanced(s.tail, c :: stk)
      case ')' => stk match { case '(' :: xs => balanced(s.tail, xs)
                              case _         => Borked }
      case ']' => stk match { case '[' :: xs => balanced(s.tail, xs)
                              case _         => Borked }
      case '}' => stk match { case '{' :: xs => balanced(s.tail, xs)
                              case _         => Borked }
      case _ => balanced(s.tail, stk)
    }

  // parse an expression or statement
  def other(x: String)(implicit e: ConsoleEnv) {
    import e.{con,supply}
    var input = x
    var blank = false
    val needMoar = StatementParsers.multiline.run(e.parseState(x), e.supply).isRight
    val verbose = Set("case","let","where")
    while ((needMoar || (balanced(input) == Unbalanced) || verbose.exists(input.contains(_))) && !blank) {
      val last = e.reader.readLine("|> ", e.reader.getEchoCharacter)
      blank = last == ""
      if (!blank) { input = input + "\n" + last }
    }
    val ps = e.parseState(input)

    val mh = ModuleHeader(
      ps.loc,
      "REPL",
      false,
      e.imports.map({
        case (m,(as, explicits, using)) => ImportExportStatement(ps.loc, false, m, as, explicits, using)
      }).toList
    )
    // now we have input
    ModuleParsers.command(mh).run(ps, e.supply.split) match {
      case Right((ps, ImportExportCommand(ImportExportStatement(loc, false, module, as, explicits, using)))) =>
        val oldSessionState = e.sessionEnv
        if (e.sessionEnv.loadedModules.contains(module)) e.importing(module, as, explicits, using)
        else {
          e.session(implicit s =>
            benchmark(loadModules(List(module))) {
              ss => "Loaded" :+: ordinal(ss.size,"module","modules")
            }
          ) match {
            case Some(n) => e.importing(module, as, explicits, using)
            case _ => ()
          }
        }

      case Right((ps, ImportExportCommand(ImportExportStatement(loc, true, module, as, explicits, using)))) =>
        writeLn("Ignoring export command")

      case Right((ps, ModuleCommand(m))) => e.session(implicit s => loadModule(ps,m))
      case Right((_, EmptyCommand)) => ()
      case Right((psp, ExpressionCommand(a))) =>
        // val at = Type.subType(e.conMap(ps), a).close
        val at = e.fixCons(psp,a).close(e.supply)
        e.subst(implicit hm => inferType(List(), at)) match {
          case Some(ty) => e.eval(at) { case r =>
            val n = e.currentResult
            val v = Global("REPL","res" + n)
            def isIO(t: Type): (Boolean, Boolean) = t match {
              case f: Forall => isIO(f.body)
              case AppT(Type.Con(_,Global("Builtin","IO",Idfix),_,_), ProductT(_,0)) => (true, true)
              case AppT(Type.Con(_,Global("Builtin","IO",Idfix),_,_), _) => (true, false)
              case _ => (false, false)
            }
            def remember {
              e.session(implicit s => primOp(ps.loc, v, r, ty))
              writeLn(nest(2, v.string :/+: ":" :/+: prettyType(ty, -1) :/+: "=" :/+: prettyRuntime(r)))
              e.currentResult = e.currentResult + 1
            }
            val (run, silent) = isIO(ty)
            if (run)
              e.sessionEnv.termNames.get(Global("IO.Unsafe","unsafePerformIO")).flatMap {
                e.sessionEnv.env.get(_)
              } match {
                case Some(unsafePerformIO) => {
                  // If our value is bottom, set the stack trace to be the wrapped error's stack trace to aid debugging.
                  val res = unsafePerformIO(r)
                  res match {
                    case Bottom(msg) =>{ try println(msg.apply.toString) catch { case t: Throwable => e.handlingBot(t) }}
                    case x => x // do nothing
                  }
                  if (silent) res.extract[Any]
                  else writeLn(prettyRuntime( res ))
                  }
                case None =>
                  writeLn("warning: IO.Unsafe.unsafePerformIO not available")
                  remember
              }
            else remember
          }
          case None => ()
        }
      case Left(err) => writeLn(err.pretty)
    }
  }

  private val command = "\\s*(\\S*)\\s*(.*)".r
  // of course with all this we don't really need the trampoline
  def repl(implicit e: ConsoleEnv) {
    e.reader.setBellEnabled(false)
    e.reader.setDefaultPrompt(">> ")
    var line: String = null
    while (!e.quit && { line = e.reader.readLine(">> ", e.reader.getEchoCharacter); line != null }) {
      e.handling(
        line match {
          case command(name, arg) if name.length > 1 =>
            actions.filter(_ matches name) match {
              case a :: _ => a(arg)
              case _ if name(0) == ':' =>
                writeLn("Unknown command: " + name.tail)
                e.helpHint
              case _ => other(line)
          }
          case _ => other(line)
        }
      )
    }
  }

  def databasePrefix: String = "Environment.DB"

  def prelude = List[String]("Prelude")

  def loadAll(xs: List[String])(implicit e: ConsoleEnv) {
    import e.{con,supply}
    if (session(implicit s => benchmark(loadModules(xs)) { ss => "Loaded" :+: ordinal(ss.size, "module","modules") }).isDefined)
      xs.foreach(importing(_))
    else writeLn("Unable to load" :/+: oxford("and", xs.map(text(_))))
  }

  def version     = "v0.4α"
  def copyright   = "Copyright 2011-2013"
  def allrights   = "McGraw Hill Financial"

  def logo(n: String, l: List[String])(implicit e: ConsoleEnv): Unit = l match {
    case l1 :: l2 :: l3 :: l4 :: rest =>
      writeLn(l1)
      writeLn(l2 + " " + n + " " + version)
      writeLn(l3 + " " + copyright)
      writeLn(l4 + " " + allrights)
      for (s <- rest) writeLn(s)
    case _ => fancyLogo // logo(ermineLogo._1, ermineLogo._2)
  }

  def ermineLogo = ("Ermine", List(
    """   ____                    """,
    """  / __/_____ _  ( )__  __  """,
    """ / _//`__/  ' \/ /`_ \/ -) """,
    """/___/_/ /_/_/_/_/_//_/\__/ """
  ))

  def fancyLogo(implicit e: ConsoleEnv) {
    writeLn("")
    writeLn("                                 _,-/\"---,")
    writeLn("          ;\"\"\"\"\"\"\"\"\"\";         _`;; \"\"  «@`---v")
    writeLn("        ; :::::  ::  \"'      _` ;;  \"    _.../")
    writeLn("       ;\"     ;;  ;;;  '\",-`::    ;;,'\"\"\"\"")
    writeLn("      ;\"          ;;;;.  ;;  ;;;  ::`    ____")
    writeLn("     ,/ / ;;  ;;;______;;;  ;;; ::,`    / __/_____ _  ( )__  __")
    writeLn("     /;; _;;   ;;;       ;       ;     / _//`__/  ' \\/ /`_ \\/ -)")
    writeLn("     | :/ / ,;'           ;_ \"\")/     /___/_/ /_/_/_/_/_//_/\\__/ " + version)
    writeLn("     ; ; / /\"\"\"=            \\;;\\\"\"=  Copyright © 2011-13 McGraw Hill Financial")
    writeLn("  ;\"\"\"';{::\"\"\"\"\"\"=            \\\"\"\"=")
    writeLn("  \\/\"\"\"")
  }

  def rock(implicit e: ConsoleEnv) {
    import e.supply
    fancyLogo
    writeLn("")
    importing("REPL")
    marked("nolib")
    val lib = session(implicit s => Lib.preamble)
    importing("Builtin")
    marked("lib")
    if (lib.isDefined) loadAll(prelude)
    else writeLn("warning: Unable to load lib.")
    e.sessionEnv.loadFile =
      SourceFile inOrder (e.sessionEnv.loadFile,
                          SourceFile filesystem Seq("core", "examples").mkString(separator))
    repl
  }

  def main(args: Array[String]) {
    com.clarifi.reporting.util.Logging.initializeLogging
    try {
      implicit val env = new ConsoleEnv(new SessionEnv)
      env.reader.getHistory.setHistoryFile(new java.io.File(".ermine_history"))
      rock
    } catch {
      case e : Throwable =>
        println("panic: " + e.getMessage)
        e.printStackTrace
    }
  }
}
