package com.clarifi.reporting
package ermine

import Document.{ text }
import scalaz._
import scalaz.Free.{ Return, suspend }
import scalaz.Scalaz._
import scala.collection.immutable.List
import com.clarifi.reporting.ermine.Diagnostic._
import java.lang.Character._
import Ordering._

import com.clarifi.reporting.util.YMDTriple.ymdPivotTimeZone

package object parsing {
  def dist[A](xs: List[Localized[A]]): Localized[List[A]] = Localized(xs.map(_.extract), xs.flatMap(_.names), xs.traverse_[Parser](_.unbind))

  def unit[A](a: A): Parser[A] = new Parser[A] {
    def apply(s: ParseState, vs: Supply) = suspend(Return(Pure(a)))
    override def map[B](f: A => B) = unit(f(a))
    override def flatMap[B](f: A => Parser[B]) = f(a)
  }

  implicit def parserDiagnostic: Diagnostic[Parser] = new Diagnostic[Parser] {
    override def raise(p: Pos, d: Document, aux: List[Document]) = Parser((_,_) => {
      val err = Err.report(p, Some(d), aux)
      // println("pending: " + err.toString) // reporting this
      err
    })
    def fail(msg: Document) = Parser((_,_) => Fail(Some(msg), List(), Set()))
    def empty = Parser((_,_) => Fail(None, List(), Set()))
  }

  implicit def parserMonad: Monad[Parser] = new Monad[Parser] {
    def point[A](a: => A) = new Parser[A] {
      def apply(s: ParseState, vs: Supply) = suspend(Return(Pure(a)))
      override def map[B](f : A => B) = pure(f(a))
    }
    override def map[A,B](m: Parser[A])(f: A => B) = m map f
    def bind[A,B](m: Parser[A])(f: A => Parser[B]) = m flatMap f
  }

  def get: Parser[ParseState] = Parser((s, _) => Pure(s))
  def gets[A](f: ParseState => A): Parser[A] = Parser((s,_) => Pure(f(s)))
  def getSupply: Parser[Supply] = Parser((_, vs) => Pure(vs))
  def loc: Parser[Pos] = Parser((s, _) => Pure(s.loc))
  def modify(f: ParseState => ParseState) = Parser((s,_) => Commit(f(s),(), Set()))
  def put(s: ParseState) = Parser((_,_) => Commit(s,(),Set()))
  def freshId = Parser((_,vs) => Pure(vs.fresh))
  def rawSatisfy(p: Char => Boolean) = Parser((s, _) => {
    val si = s.input
    if (s.offset == si.length) Fail(None, List(), Set())
    else {
      val so = s.offset
      val c = si.charAt(so)
      val sop = so + 1
      if (p(c)) Commit(s.copy(loc = s.loc.bump(c, si, sop), offset = sop), c, Set())
      else Fail(None, List(), Set())
    }
  })
  def satisfy(p: Char => Boolean) = rawSatisfy(p) << setBol(false)

  def realEOF: Parser[Unit] = Parser((s, _) =>
    if (s.offset == s.input.length) Pure(())
    else Fail(None, List(), Set("end of input"))
  )

  def warn(msg: Document) = Parser((s, _) => { println(msg.toString); Pure(()) })
  def info(msg: Document) = Parser((s, _) => { println(msg.toString); Pure(()) })

  def choice[A](xs: Parser[A]*) = xs.toList.foldRight[Parser[A]](empty)(_ | _)
  def assert(p: => Boolean): Parser[Unit] = if (p) unit(()) else empty
  def attempt[A](p: Parser[A]) = p attempt
  def attempt[A](p: Parser[A], s: String) = p attempt s
  def liftOption[A](p: Option[A]): Parser[A] = p match {
    case Some(a) => unit(a)
    case None    => empty
  }
  def handle[A](p: Parser[A], f: ParseFailure => Parser[A]): Parser[A] = p handle f
  def notFollowedBy[A](p: Parser[A]) = p not

  def stillOnside: Parser[Unit] = for {
    b <- gets(s => !s.bol || s.loc.column > s.depth)
    _ <- guard[Parser](b)
  } yield ()

  def rawCh(c: Char): Parser[Char] = rawSatisfy(_ == c) scope ("'"+c.toString+"'")
  implicit def ch(c: Char): Parser[Char] = stillOnside >> rawCh(c) << setBol(false)
  def rawNewline = rawSatisfy(_ == '\n') scope "newline"
  // def tab = rawSatisfy(_ == '\t') scope "tab"
  def rawWord(s: String): Parser[String] = s.toList.traverse[Parser,Char](ch(_)) attempt ('"'+s+'"') as s
  implicit def word(s: String): Parser[String] = stillOnside >> rawWord(s) << setBol(false)

  def upper  = satisfy(_.isUpper) scope "uppercase letter"
  def lower  = satisfy(_.isLower) scope "lowercase letter"
  def letter = satisfy(_.isLetter) scope "letter"
  def rawLetter = rawSatisfy(_.isLetter) scope "letter"
  def digit  = satisfy(_.isDigit) scope "digit"
  def simpleSpace = satisfy(java.lang.Character.isWhitespace(_)) scope "simple space"

  // layout
  def setBol(b: Boolean): Parser[Unit] = for {
    old <- gets(_.bol)
    _ <- modify(s => s.copy(bol = b)).when(old != b) // avoid committing if we haven't changed it
  } yield ()

  private def pushContext(ctx: LayoutContext): Parser[Unit] = modify { s => s.copy(layoutStack = ctx :: s.layoutStack) }

  private def popContext(msg: String, f: LayoutContext => Boolean): Parser[Unit] = for {
    u <- get
    if !u.layoutStack.isEmpty
    l <- loc
    _ <- put(u.copy(layoutStack = u.layoutStack.tail))
  } yield ()

              // TODO: properly parse and check for operators that start with --
  private def comment: Parser[Unit] = rawWord("--").attempt >> rawSatisfy(_ != '\n').skipMany >> (rawNewline | realEOF) >> unit(())
  private def blockComment: Parser[Boolean] = {
    def restComment(hadnl: Boolean): Parser[Boolean] =
      rawWord("-}").attempt.as(hadnl) |
      (blockComment >>= restComment) |
      ((rawSatisfy(_ != '\n').as(hadnl) | rawNewline.as(true)) >>= restComment)
    rawWord("{-").attempt >> restComment(false)
  }
  private def someRealWhitespace = rawSatisfy(x => java.lang.Character.isWhitespace(x) && x != '\n').skipSome
  def whiteSpace(spaced: Boolean, side: Boolean): Parser[Token] =
    ( comment.as(true)
    | blockComment
    | rawNewline.as(true)
    | someRealWhitespace.as(false)
    ).scope("whitespace").many.flatMap {
      case List() if side                  => offside(spaced)
      case List()                          => onside (spaced)
      case xs if xs.foldLeft(side)(_ || _) => offside(true)
      case xs                              => onside (true)
    }
  private def offside(spaced: Boolean) = get.flatMap(s => {
    val col = s.loc.column
    s.layoutStack match {
      case IndentedLayout(n, _) :: xs => (col ?|? n) match {
        case LT => modify(_.copy(layoutStack = xs, bol = true)) as VBrace // pop the layout stack, and we're at bol
        case EQ => if (s.offset != s.input.length) setBol(false) as VSemi
                   else unit(Other)
        case GT => onside(spaced)
      }
      case _ => onside(spaced)
    }
  })

  private def onside(spaced: Boolean): Parser[Token] = get.flatMap(s => {
    if (s.offset == s.input.length)
      s.layoutStack match {
        case IndentedLayout(n, desc) :: xs    => modify(_.copy(layoutStack = xs, bol = true)) as VBrace
        case BracedLayout(_,_,missing,_) :: _ => missing
        case List()                           => unit(Other)
      }
    else s.layoutEndsWith.wouldSucceed.flatMap { b =>
      if (b)
        s.layoutStack match {
          case IndentedLayout(_,desc) :: xs => modify(_.copy(layoutStack = xs, bol = true)) as VBrace
          case _ => if (spaced) unit(WhiteSpace)
                    else setBol(false) as Other
        }
      else if (spaced) unit(WhiteSpace)
           else setBol(false) as Other
    }
  })

  def layout: Parser[Token] = get.flatMap(s => whiteSpace(false, s.bol))

  def virtualLeftBrace(n: String): Parser[Unit] =
    modify(s => s.copy(layoutStack = IndentedLayout(s.loc.column max s.depth, n) :: s.layoutStack))

  def virtualRightBrace: Parser[Unit] = get.flatMap(s =>
    layout.flatMatch({
      case VBrace => unit(unit(())) // the layout parser already popped our stack
      case VSemi => loc.flatMap(p => unit(raise(p, "panic: trailing virtual semicolon")))
      case Other|WhiteSpace => for {
        sp <- get
        b <- sp.layoutEndsWith.wouldSucceed
        _ <- failUnless[Parser](b,"end of layout not found")
      } yield raiseWhen[Parser](sp.layoutStack.isEmpty || sp.layoutStack.head.isInstanceOf[BracedLayout], sp.loc, "panic: incorrect layout context for virtual right brace") >>
              modify(_.copy(layoutStack = sp.layoutStack.tail)) // bol remains false
    }).attempt(
      s.layoutStack.collectFirst({
        case BracedLayout(l, _, _, r) => "end of layout (between '" + l + "' and '" + r + "')"
      }).getOrElse("end of layout")
    ).flatMap(x => x)
  )
  // <interactive>:3:3: error: unmatched '{'
  // <interactive>:5:6: note: expected '}'
  // <interactive>:5:6: error: expected infixl (<=) 6 term, end of top level layout, or ...

  // TODO: allow right to succeed when the closing brace parser fails in a 'corrected' mode that can only consume text and report further errors?
  def left(lp: Parser[Any], ld: String, rp: Parser[Any], rd: String): Parser[Unit] = for {
    start <- loc
    _ <- lp.scope(ld)
    _ <- modify(s =>
      s.copy(
        layoutStack = BracedLayout(
          ld,
          rp.scope(rd),
          Parser((s, _) => Fail(None,List(start.report("note: unmatched " + ld)), Set(rd))),
          // l => raise(start, "error: unmatched " + ld, List(l.report("note: expected corresponding " + rd + " here"))),
          rd
        ) :: s.layoutStack
      )
    )
  } yield ()

  def leftLet      = left(keyword("let"),"let", rawKeyword("in"), "in")
  def leftCase     = left(keyword("case"),"case", rawKeyword("of"), "of")
  def leftToken(ld: String, rd: String) = left(token(ld), "'" + ld + "'", rawWord(rd), "'" + rd + "'")
  def leftBrace    = leftToken("{","}")
  def leftCurlyBanana = leftToken("{|","|}")
  def leftBracket  = leftToken("[","]")
  def leftBanana   = leftToken("(|","|)")
  def leftEnvelope = leftToken("[|","|]")

  def right: Parser[Unit] = get.flatMap { s =>
    s.layoutStack match {
      case b@BracedLayout(_,p,missing,r) :: xs =>
        (  p.scope(r) >>
           modify(_.copy(layoutStack = xs)) >>
           optionalSpace.skipOptional
        ) | missing
      case stk => raise(s.loc, "panic: expected braced layout, but found: " + stk.mkString(",")) // , but found:" above nest(2, vsep(stk.map(text(_.toString)))))
    }
  }

  def semi: Parser[Char] = layout.flatMatch({
    case Other => token(';')
    case VSemi => unit(';')
  }).attempt("semicolon")

  def eofIgnoringLayout: Parser[Unit] = realEOF // eof // realEOF

  // def eof: Parser[Unit] = realEOF scope "eof" // | layout.flatMatch({ case EOF => unit(()) }) attempt "eof"

  def optionalSpace: Parser[Unit] = layout.flatMatch({
    case WhiteSpace => unit(())
    case Other => unit(())
    case VSemi => Diagnostic.fail("vsemi in optional space")
    case VBrace => Diagnostic.fail("vbrace in optional space")
  }) attempt "whitespace"

  def eof: Parser[Unit] = realEOF scope "eof" // (layout.collect({ case WhiteSpace | Other => ()}).attempt.skipOptional >> realEOF) scope "end of input"

  def laidout[T](s: String, p: Parser[T]): Parser[List[T]] = (
    brace(p.scope(s).sepBy(token(';'))) |
    p.scope(s).sepBy(semi).between(virtualLeftBrace(s), virtualRightBrace)
  ) scope "layout(" + s + ")"

  def phrase[A](p: Parser[A]) = modify(_.copy(layoutStack = List())) >> simpleSpace.skipMany >> p << eof
  def token[A](p: => Parser[A]): Parser[A] = p << optionalSpace.skipOptional
  def banana[A](p: => Parser[A]): Parser[A] = p.between(leftBanana,right)
  def paren[A](p: => Parser[A]): Parser[A] = p.between(leftToken("(",")"),right)
  def brace[A](p: => Parser[A]): Parser[A] = p.between(leftBrace,right)
  def bracket[A](p: => Parser[A]): Parser[A] = p.between(leftBracket,right)
  def envelope[A](p: => Parser[A]): Parser[A] = p.between(leftEnvelope, right)
  def curlyBanana[A](p: => Parser[A]): Parser[A] = p.between(leftCurlyBanana, right)

  private val charEscMagic: Map[Char, Char] = "bfnrt\\\"'".zip("\b\f\n\r\t\\\"'").toMap
  private val charEscUnmagic: Map[Char, Char] = charEscMagic map (_.swap)

  private def charControl  = (ch('^') >> upper).map(c => (c.toInt - 'A'.toInt).toChar)
  private def charEsc      = choice(charEscMagic.toSeq.map { case (c,d) => ch(c) as d } :_*)
  private def escapeCode   = (charControl | charEsc) scope "escape code" // TODO: charNum, charAscii
  private def charEscape   = ch('\\') >> escapeCode
  private def charLetter   = satisfy(c => (c != '\'') && (c != '\\') && (c > '\026'))
  private def charChar     = (charLetter | charEscape) scope "character literal character"
  private def stringLetter = satisfy(c => (c != '"') && (c != '\\') && (c > '\026'))
  private def stringEscape = ch('\\') >> (
    (simpleSpace.skipSome >> (ch('\\') scope "end of string gap")).as(None) | // escape gap
    ch('&').as(None) |                                                  // empty escape
    escapeCode.map(Some(_))
  )
  private def stringChar = (stringLetter.map(Some(_)) | stringEscape) scope "string literal character"

  /** token parser for parsing a character literal */
  def charLiteral = token(charChar.between('\'','\'') scope "character literal")

  /** token parser for parsing a string literal */
  // def stringLiteral: Parser[String] = satisfy('"' != _).skipMany.slice.between('"', '"')
  def stringLiteral: Parser[String] = token(stringChar.many.between('"','"').map(
    _.sequence[Option,Char].getOrElse(List()).mkString
  ) scope "string literal")

  /** Format a string back to its equivalent literal form. */
  def inverseStringLiteral(s: String): String =
    "\"" |+| augmentString(s).flatMap{
      case c if charEscUnmagic contains c => "\\" + charEscUnmagic(c)
      case c if 1 to 26 contains c => "^" + (c + ('A' - 1) toChar)
      case c => c.toString} |+| "\""

  def doubleLiteral_ : Parser[Double] = (digit.skipSome >> (((ch('.') >> digit.skipMany) >> (ch('e') >> digit.skipSome).skipOptional) | ((ch('e') >> digit.skipSome)))).attempt.slice.map(_.toDouble)
  def doubleLiteral: Parser[Double] = token(doubleLiteral_)

  def dateLiteral_ = {
    val oneToNine = satisfy("123456789" contains (_:Char))
    for {
      y <- ch('@') >> nat_ << ch('/')
      m <- nat_.filter(1 to 12 contains) << ch('/')
      d <- nat_.filter(1 to 31 contains)
    } yield {
      import java.util.Calendar
      val c = Calendar getInstance ymdPivotTimeZone
      c set (Calendar.MILLISECOND, 0)
      c set (y.toInt, m.toInt - 1, d.toInt, 0, 0, 0)
      c.getTime
    }}
  /** token parser for date literals
    * (dates being year-month-day triples) */
  def dateLiteral = token(dateLiteral_.attempt)

  def nat_ = digit.skipSome.slice.map(_.toLong)
  def nat = token(nat_)
  def tailChar: Parser[Char] = satisfy(c => c.isLetter || c.isDigit || c == '_' || c == '#' || c == '\'')
  def rawTailChar: Parser[Char] = rawSatisfy(c => c.isLetter || c.isDigit || c == '_' || c == '#' || c == '\'')
  def identTail: Parser[Unit] = tailChar.skipMany
  def rawIdentTail: Parser[Unit] = rawTailChar.skipMany

  val nonopChars = "()[]{};,\"".sorted.toArray[Char]
  val opChars = ":!#$%&*+./<=>?@\\^|-~'`".sorted.toArray[Char]
  def existsIn(chs: Array[Char], c: Char): Boolean =
    java.util.Arrays.binarySearch(chs, c) >= 0
  def isOpChar(c: Char) =
    existsIn(opChars, c) ||
    (!existsIn(nonopChars, c) && punctClasses(c.getType.asInstanceOf[Byte]))

  def opChar: Parser[Char] = satisfy(isOpChar(_))
  def keyword(s: String): Parser[Unit] = token((letter >> identTail).slice.filter(_ == s).skip.attempt(s))
  def rawKeyword(s: String): Parser[Unit] = (stillOnside >> rawLetter >> rawIdentTail).slice.filter(_ == s).skip.attempt("raw " + s)

  // keywords which cannot be used as identifiers
  val unusedKeywords   = Set("subtype")
  val otherKeywords    = Set("exists", "constructor", "do", "forall", "phi", "φ", "prj#", "rho", "ρ", "constraint", "Γ", "table", "where", "infixr", "infixl", "infix", "postfix", "prefix", "case", "let", "in", "of", "esac", "subtype", "hole", "Eval")
  val startingKeywords = Set("private", "abstract", "field", "data", "foreign", "type", "import", "export", "database","class","instance")
  val keywords = startingKeywords ++ otherKeywords ++ unusedKeywords
  val field      = keyword("φ") | keyword("phi")
  val constraint = keyword("Γ") | keyword("constraint")
  val rhoS       = keyword("ρ") | keyword("rho")

  private val punctClasses = Set(
    START_PUNCTUATION, END_PUNCTUATION, DASH_PUNCTUATION,
    INITIAL_QUOTE_PUNCTUATION, FINAL_QUOTE_PUNCTUATION,
    MATH_SYMBOL, CURRENCY_SYMBOL, MODIFIER_SYMBOL, OTHER_SYMBOL
  )

  /** token parser that consumes a key operator */
  def keyOp(s: String): Parser[Unit] = token((opChar.skipSome).slice.filter(_ == s).skip.attempt("'" + s + "'"))

  // key operators which cannot be used by users
  val keyOps = Set(":", "=","..","->","=>","~","<-") // "!" handled specially
  val star   = keyOp("*") // NB: we permit star to be bound by users, so it isn't in keyOps

  val doubleArrow = keyOp("=>")
  val ellipsis    = keyOp("..")
  val colon       = keyOp(":")
  val dot         = keyOp(".")
  val backslash   = keyOp("\\")
  val bang        = keyOp("!")
  val comma       = token(ch(',')) as ","
  def prec: Parser[Int] = nat.filter(_ <= 10L).map(_.toInt) scope "precedence between 0 and 10"
  def underscore: Parser[Unit] = token((ch('_') >> notFollowedBy(tailChar)) attempt "underscore")

  // kinds
  def prefix (n: String, p: Int = 10) = Local(n, Prefix(p))
  def postfix(n: String, p: Int = 10) = Local(n, Postfix(p))
  def infix  (n: String, p: Int = 9, a: Assoc = AssocL) = Local(n, Infix(p,a))
}
