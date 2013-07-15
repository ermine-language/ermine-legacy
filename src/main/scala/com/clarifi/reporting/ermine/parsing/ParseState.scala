package com.clarifi.reporting.ermine.parsing

import com.clarifi.reporting.ermine._

import scala.collection.immutable.List
import scala.collection.immutable.TreeSet
import scalaz.{ Name => _, _ }
import scalaz.Scalaz._
import scalaz.Lens._
import com.clarifi.reporting.ermine.syntax.{Renaming, Single, Explicit}

/** Used to track the current indentation level
  *
  * @author EAK
  */

case class ParseState(
  loc:            Pos,
  input:          String,
  moduleName:     String,
  offset:         Int = 0,
  canonicalTerms: Map[Local, Name] = Map(), // used to patch up fixity and to globalize local names
  canonicalTypes: Map[Local, Name] = Map(), // "
  termNames:      Map[Name, V[Type]] = Map(),
  typeNames:      Map[Name, V[Kind]] = Map(),
  kindNames:      Map[Name, V[Unit]] = Map(),
  layoutStack:    List[LayoutContext] = List(IndentedLayout(1,"top level")),
  bol:            Boolean = false
) extends Located {
  def depth: Int = layoutStack match {
    case IndentedLayout(n,_)   :: _ => n
    case BracedLayout(_,_,_,_) :: _ => 0
    case List()                     => 0
  }
  def layoutEndsWith: Parser[Any] = layoutStack.collectFirst({ case p : BracedLayout => p.endsWith }).getOrElse(eofIgnoringLayout scope "end of top level layout")
  def tracing = true // if we ever add an option we can add it to the case class
  def importing(sessionTerms: Map[Global,TermVar], cons: Set[Global], m: Map[String, (Option[String], List[Explicit], Boolean)]) = {
    def imported(isType: Boolean, g: Global): Boolean = m.get(g.module) match {
      case Some((_, explicit, using)) =>
        if(using) // using: only import things mentioned explicitly
          explicit.exists(e => g == e.global && isType == e.isType)
        else // hiding: don't import things mentioned explicitly unless they're renamed
          explicit.forall {
            case Single(n,t) => n != g || isType != t
            case _           => true
          }
      case None => false
    }
    def local(isType: Boolean): PartialFunction[Global,(Local,Global)] = {
      case (g: Global) if imported(isType, g) => m(g.module) match {
        case (as, explicits, _) => (g.localized(as, Explicit.lookup(g, explicits.filter(_.isType == isType))), g)
      }
    }
    def ordering = scala.math.Ordering[(String, String, String)].on[(Local,Global)]({ case (l,g) => (l.string, g.module, g.string) })
    copy(
      // toMap depends on the order, whereas TreeSet guarentees a unique ordering.
      canonicalTerms = canonicalTerms ++ (TreeSet()(ordering) ++ sessionTerms.keySet.collect(local(false))).toMap,
      canonicalTypes = canonicalTypes ++ (TreeSet()(ordering) ++ cons.collect(local(true))).toMap,
      termNames = termNames ++ sessionTerms
    )
  }
}

/** LayoutContext are used to track the current indentation level for parsing */
sealed abstract class LayoutContext
case class IndentedLayout(depth: Int, desc: String) extends LayoutContext {
  override def toString = "indented " + desc + " (" + depth + ")"
}
case class BracedLayout(left: String, endsWith: Parser[Any], unmatchedBy: Parser[Nothing], right: String) extends LayoutContext {
  override def toString = left + " " + right
}

object ParseState {
  def mk(filename: String, content: String, module: String) = {
    ParseState(
      loc = Pos.start(filename, content),
      input = content,
      moduleName = module
    )
  }

  private def kindNamesLens = Lens[ParseState, Map[Name, V[Unit]]](s => Store(n => s.copy (kindNames = n), s.kindNames))
  private def typeNamesLens = Lens[ParseState, Map[Name, V[Kind]]](s => Store(n => s.copy (typeNames = n), s.typeNames))
  private def termNamesLens = Lens[ParseState, Map[Name, V[Type]]](s => Store(n => s.copy (termNames = n), s.termNames))
  private def canonicalTermsLens = Lens[ParseState, Map[Local, Name]](s => Store(n => s.copy (canonicalTerms = n), s.canonicalTerms))
  private def canonicalTypesLens = Lens[ParseState, Map[Local, Name]](s => Store(n => s.copy (canonicalTypes = n), s.canonicalTypes))
  object Lenses {
    def kindNames      = kindNamesLens
    def typeNames      = typeNamesLens // These would be inline, but !@&*#(& scala
    def termNames      = termNamesLens
    def canonicalTerms = canonicalTermsLens
    def canonicalTypes = canonicalTypesLens
  }
}
