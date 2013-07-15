package com.clarifi.reporting.ermine.parsing
import ParseState.Lenses._
import com.clarifi.reporting.ermine.Diagnostic._
import TypeParsers.unspecifiedType
import com.clarifi.reporting.ermine._

trait TermNameParser extends NameParser {
  def termName: Parser[Name]      = get.flatMap(u => name(u.canonicalTerms))
  def localTermName: Parser[Name] = get.flatMap(u => localName(u.canonicalTerms))

  // top level definitions which bind local names
  // ->foo<- : Int
  // data ->Foo<- a b c = ->Bar<- Int a
  def termDef: Parser[TermVar] = for {
    p <- loc
    n <- termName
    _ <- if (!n.isInstanceOf[Local]) raise(p, "error: term definition would shadow global definition " + n)
         else unit(())
    l =  termNames.member(n)
    m <- gets(l.get(_))
    r <- m match {
      case Some(v) =>
        val vp = v at p
        modify(l.set(_, Some(vp))) as vp // update the term map to point to the _actual_ definition location for future reference
      case None => for {
        k <- unspecifiedType(p)
        v <- freshId.map(V(p,_,Some(n),Bound,k))
        _ <- modify(l.set(_, Some(v)))
      } yield v
    }
  } yield r

  def termOpVar(fix: Fixity, f : Fixity => Boolean): Parser[TermVar] = attempt(
    for {
      p <- loc
      s <- op
      Some(n) <- gets(_.canonicalTerms.get(Local(s,fix)))
      if f(n.fixity) // == fix
      l = termNames.member(n)
      m <- gets(l.get(_))
      r <- m match {
        case Some(v) => unit(v at p)
        case None => for {
          k <- unspecifiedType(p)
          v <- freshId.map(V(p,_,Some(n),Bound,k))
          _ <- modify(l.set(_, Some(v)))
        } yield v
      }
    } yield r,
    fix match {
      case Idfix => "identifier"
      case Prefix(_) => "prefix term operator"
      case _ => "term operator"
    }
  )

  def termOp(fix: Fixity, f : Fixity => Boolean): Parser[Var] = for {
    p <- loc
    v <- termOpVar(fix, f)
  } yield Var(v at p)

  // term variables inside of a term somewhere which use local or global names
  def termVar: Parser[TermVar] = for {
    p <- loc
    n <- termName
    l = termNames.member(n)
    m <- gets(l.get(_))
    r <- m match {
      case Some(v) => unit(v at p)
      case None => for {
        k <- unspecifiedType(p)
        v <- freshId.map(V(p,_,Some(n),Bound,k))
        _ <- modify(l.set(_, Some(v)))
      } yield v
    }
  } yield r
}

// can recognize any name, upper or lower case
object TermNameParsers extends TermNameParser {
  def identStart = letter
  def opStart = opChar
}

/** Names suitable for signing or term definition. */
object TermBindingParsers extends TermNameParser {
  def identStart = lower
  def opStart = opChar
}

object DataConParsers extends TermNameParser {
  def identStart = upper
  def opStart = ch(':')
}

object PatternVarParsers extends TermNameParser {
  def identStart = lower
  def opStart = satisfy(c => c != ':' && isOpChar(c))
}
