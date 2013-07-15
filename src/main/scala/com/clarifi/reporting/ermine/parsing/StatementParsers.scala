package com.clarifi.reporting.ermine.parsing

import java.util.Date
import java.text.DecimalFormat
import com.clarifi.reporting.ermine.syntax._
import com.clarifi.reporting.ermine.syntax.Statement.{ gatherBindings, checkBindings }
import TermNameParsers._
import TypeParsers._
import TermParsers._
import ParseState.Lenses._
import PatternParsers.manyPatterns
import ModuleParsers.moduleName
import KindParsers.localKind
import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Diagnostic._
import com.clarifi.reporting.ermine.Type.typeVars
import com.clarifi.reporting.ermine.Term.termVars
import com.clarifi.reporting.ermine.HasTypeVars._
import scalaz.{ Name => _, _ }
import scalaz.Scalaz._
import scala.collection.immutable.List
import scala.collection.mutable.{ HashMap, SynchronizedMap }

object StatementParsers {
  private val sig: Parser[(TermVar,Type)] = (TermBindingParsers.termDef << keyOp(":")) ++ typ
  private val dataConSig: Parser[(TermVar,Type)] = (DataConParsers.termDef << keyOp(":")) ++ typ

  // backtrackable up to the :
  private val sigs: Parser[(List[TermVar],Type)] = (TermBindingParsers.termDef.sepBy(comma) << keyOp(":")).attempt ++ typ

  val fieldDef: Parser[TypeVar] = for {
    p <- loc
    n <- ident
    cn <- gets(_.canonicalTypes.get(n)) // does it canonicalize to a global?
    mod <- gets(_.moduleName)
    n <- cn match {
      case Some(g : Global) => raise(p, "error: field definition would shadow global type definition")
      case Some(l : Local)  => unit(l)
      case None => unit(n)
    }
    l = typeNames.member(n)
    m <- gets(l.get(_))
    r <- m match {
      case Some(v) => unit(v)
      case None => for {
        v <- freshId.map(V(p,_,Some(n),Bound,Rho(p.inferred)))
        _ <- modify(l.set(_, Some(v)))
      } yield v
    }
  } yield r

  val fieldSig: Parser[TypeVar] = for {
    p <- loc
    n <- ident
    id <- freshId
    l = typeNames.member(n)
    old <- gets(l.get(_))
    v = V(p, id, Some(n), Bound, Rho(p.inferred))
    _ <- modify(l.set(_, Some(v)))
  } yield v

  def explicit(module: String): Parser[Explicit] = for {
    p <- loc
    isTy <- keyword("type").optional map (_.isDefined)
    src <- name({ case l => l }).map(_.global(module))
    on <- (keyword("as") >> name({ case l => l })).optional
    _ <- on match {
      case Some(rename) if src.fixity.con != rename.fixity.con =>
        raise(p, "error: Renaming to different operator type is not supported.")
      case _ => unit(())
    }
  } yield on match {
      case Some(rename) => Renaming(src, rename, isTy)
      case None         => Single(src, isTy)
    }

  val importExportStatement: Parser[ImportExportStatement] = (for {
    p <- loc
    export <- keyword("import").as(false) | keyword("export").as(true)
    src <- moduleName // stringLiteral
    as <- (keyword("as") >> ident.map(_.string)).optional
    opt <- (for {
      using <- keyword("using").as(true) | keyword("hiding").as(false)
      exps <- laidout("explicit imports", explicit(src))
    } yield (using, exps)).optional
  } yield opt match {
    case Some((using, exps)) => ImportExportStatement(p, export, src, as, exps, using)
    case None                => ImportExportStatement(p, export, src, as)
  }) scope "import/export statement"

  /**   table foo, bar : baz
    or: table dbo.foo, sys.dbo.bar : baz */
  private def tableStatement(dbName: String) = for {
    p <- loc << keyword("table")
    vs ++ t <- (((TermNameParsers.termName << dot).attempt.many ++ TermNameParsers.termDef).sepBy1(comma) << keyOp(":")).attempt ++ typ
  } yield TableStatement(p, dbName, vs, t)

  def sameLine(p: Pos) = Parser((s,_) => if (s.loc.line == p.line) Pure(()) else Fail())

  // TODO: private class blocks, and private class members
  private val privateBlock = for {
    p <- loc << keyword("private")
    foreign <- (sameLine(p) >> keyword("foreign")) as true orElse false
    r <- if (foreign) for {
            ss <- laidout("private foreign statement", foreignStatement)
         } yield PrivateBlock(p, List(ForeignBlock(p, ss)))
         else for {
           ss <- laidout("private statement", statement)
         } yield PrivateBlock(p, ss)
  } yield r

  private val foreignBlock = for {
    p <- loc << keyword("foreign")
    privat <- (sameLine(p) >> keyword("private")) as true orElse false
    ss <- laidout("foreign statement", foreignStatement)
  } yield if (privat) ForeignBlock(p, List(PrivateBlock(p, ss)))
          else ForeignBlock(p, ss)

  private val foreignPrivateBlock = for {
    p <- loc << keyword("private")
    ss <- laidout("foreign private statement", foreignStatement)
  } yield PrivateBlock(p, ss)

  private val databaseBlock = for {
    p <- loc << keyword("database")
    db <- stringLiteral
    ss <- laidout("database statement", tableStatement(db))
  } yield DatabaseBlock(p, db, ss)

  private val classPrivateBlock = for {
    p <- loc << keyword("private")
    ss <- laidout("class private statement", bindingStatement)
  } yield PrivateBlock(p, ss)

  /*
     infix 4 == /= <= >= < >

     class Eq a where
       (==) :: a -> a -> Bool
       (/=) :: a -> a -> Bool
       x /= y = not (x == y)

     data Ordering = LT | EQ | GT

     class Ord a | Eq a where
       compare :: a -> a -> Ordering

       (<=)    :: a -> a -> Bool
       (>=)    :: a -> a -> Bool
       (<)     :: a -> a -> Bool
       (>)     :: a -> a -> Bool
       min     :: a -> a -> a
       max     :: a -> a -> a

       x <= y = case compare x y of
         GT -> False
         _  -> True
       x >= y = case compare x y of
         LT -> False
         _  -> True
       x < y = case compare x y of
         LT -> True
         _  -> False
       x > y = case compare x y of
         GT -> True
         _  -> False
       min x y = case compare x y of
         GT -> y
         _  -> x
       max x y = case compare x y of
         LT -> y
         _  -> x
  */

  private val classBlock = for {
    p <- loc << keyword("class")
    nm <- typeDef
    lks <- brace(manyDistinct(localKind)).orElse(Localized(List()))
    r <- localTypes(vs => for {
         ctx <- (keyOp("|") >> typL2.sepBy1(comma)) orElse List()
         rss <- (keyword("where") >> laidout("class body", classPrivateBlock | bindingStatement)) orElse List()
       } yield ClassBlock(p, nm, lks.extract, vs, ctx,
         rss.collect({ case t : PrivateBlock => t.definedTerms }).foldLeft(Set():Set[TermVar])(_++_),
         rss.flatMap {
           case t : PrivateBlock => t.statements.collect { case t : BindingStatement => t }
           case t : BindingStatement => List(t)
           case _ => List() // OMGWTFPolarBear
         }
       )
    )
    _ <- lks.unbind
  } yield r

  /** foo, bar : baz */
  private val sigStatement = for {
    p <- loc
    vs ++ t <- sigs
  } yield SigStatement(p, vs, t)
  /** foo x y z = bar x y z */
  private val termStatement = for {
    p <- loc
    v <- TermBindingParsers.termDef
    r <- manyPatterns {
      pats => for {
        body <- keyOp("=") >> term
        lw <- loc
        clause <- (keyword("where") >> laidout("binding statement", bindingStatement)).optional
        r <- clause match {
          case None => unit(body)
          case Some(ss) =>
            val (is, sigs) = gatherBindings(ss)
            for {
              p <- checkBindings[Parser](lw, is, sigs)(parserMonad, parserDiagnostic)
              _ <- p.distinct(lw)
              _ <- p.unbind // I assume we want to add this here - EDS
            } yield Let(lw, p.extract._1, p.extract._2, body)
        }
      } yield TermStatement(p, v, pats, r)
    }
  } yield r

  /** Parses a fixity declaration of the form:
   *
   *  postfix type 10 *
   *
   *  as an appropriate name together with a boolean representing whether 'type' appeared.
   */
  private val fixityStatement = for {
    p <- loc
    f <- (keyword("prefix")  as (Prefix (_))) |
         (keyword("postfix") as (Postfix(_))) |
         (keyword("infixr")  as (InfixR (_))) |
         (keyword("infixl")  as (InfixL (_))) |
         (keyword("infix")   as (InfixN (_)))
    t <- keyword("type") as true orElse false
    i <- prec
    ops <- op.many
    ns <- ops.traverse[Parser, Local] { op =>
      val n = Local(op, f(i))
      addFixity(n, t) as n
    }
  } yield FixityStatement(p, ns, t)

  // field foo, bar : type
  private val fieldStatement = for {
    p <- loc << keyword("field")
    vs <- fieldDef.sepBy1(comma) << keyOp(":")
    t <- typ
  } yield FieldStatement(p,vs,t)

  private val typeStatement = for {
    p <- loc << keyword("type")
    v <- typeDef
    lks <- brace(manyDistinct(localKind)).orElse(Localized(List()))
    r <- localTypes(vs => keyOp("=") >> anyTyp.map(TypeStatement(p,v,lks.extract,vs,_)))
    _ <- lks.unbind
  } yield r

  // TODO: parse an expression and extract the root
  private val dataCon0: Parser[(TermVar, List[Type])] = DataConParsers.termDef ++ typL0.many
  private val dataCon: Parser[(List[TypeVar], TermVar, List[Type])] =
    (keyword("forall") >>
    localTypes(vs =>
      keyOp(".") >> dataCon0 map { case (p, q) => (vs, p, q) }
    )) | (dataCon0 map { case (p, q) => (List(), p, q) })

  private val dataStatement = for {
    p <- loc
    v <- keyword("data") >> typeDef
    lks <- brace(manyDistinct(localKind)).orElse(Localized(List()))
    r <- localTypes(vs => for {
        cons <- (keyOp("=") >> dataCon.sepBy1(keyOp("|"))) orElse List() // TODO: optional keyword private before each data con
      } yield DataStatement(p, v, lks.extract, vs, cons)
    )
    _ <- lks.unbind
  } yield r

  // global cache used because the classLoader doesn't seem to cache these across threads
  val classMap = new HashMap[String, Class[T] forSome {type T}] with SynchronizedMap[String, Class[T] forSome {type T}]
  def classLookup(p: Pos, s: String): Either[Exception,ForeignClass] = {
    // val then = System.nanoTime
    classMap.get(s) match {
      case Some(c) => Right(ForeignClass(p, c))
      case None    =>
        val c = try { Right(Class.forName(s)) }
                catch { case e:Exception => Left(e) }
        // val df = new DecimalFormat("0.0000");
        // println("class lookup of " + s + " took " + df.format((System.nanoTime - then)/1000000000.0) + "s")
        c.right.map { c =>
          classMap += (s -> c)
          ForeignClass(p, c)
        }
    }
  }

  // convert a string into a Class[_] if possible
  private val clazz: Parser[ForeignClass] = for {
    p <- loc
    s <- stringLiteral scope "foreign class name"
    r <- classLookup(p, s) match {
      case Right(c) => unit(c)
      case Left(e) => raise(p, "error loading '"+s+"'", List("cause: " + e.toString))
    }
  } yield r

  private val foreignData = for {
    p <- loc
    cls <- keyword("data") >> clazz
    v <- typeDef
    r <- localTypes(vs => unit(ForeignDataStatement(p,v,vs,cls)), p => unit(Star(p)))
  } yield r

  private val member: Parser[ForeignMember] =
    loc.map2(stringLiteral scope "foreign member name")(ForeignMember(_,_))

  private val foreignMethod = for {
    p <- loc << keyword("method")
    m <- member
    v ++ t <- sig
  } yield ForeignMethodStatement(p, v, t, m)

  private val foreignFunction = for {
    p <- loc << keyword("function")
    cls <- clazz
    m <- member
    v ++ t <- sig
  } yield ForeignFunctionStatement(p, v, t, cls, m)

  private val foreignValue = for {
    p <- loc << keyword("value")
    cls <- clazz
    m <- member
    v ++ t <- sig
  } yield ForeignValueStatement(p, v, t, cls, m)

  private val foreignConstructor = for {
    p <- loc << keyword("constructor")
    v ++ t <- sig
  } yield ForeignConstructorStatement(p, v, t)

  private val foreignSubtype = for {
    p <- loc << keyword("subtype")
    v ++ t <- dataConSig
  } yield ForeignSubtypeStatement(p, v, t)

  val bindingStatement: Parser[BindingStatement] =
    sigStatement |
    termStatement // | emptyStatement

  val foreignStatement: Parser[Statement] =
      foreignData        |
      foreignMethod      |
      foreignValue       |
      foreignFunction    |
      foreignConstructor |
      foreignSubtype     |
      foreignPrivateBlock

  val statement: Parser[Statement] = (
    fixityStatement    | // (prefix|postfix|infix(r|l)?) type? 10 foo
    fieldStatement     | // field foo : bar
    tableStatement("") | // table foo : bar
    typeStatement      | // type foo x y z = bar x y z
    dataStatement      | // (abstract?) data Foo a b c = Foo a b c | Bar a b c
    foreignBlock       |
    privateBlock       |
    databaseBlock      |
    classBlock         |
    bindingStatement     // foo : bar  or foo x y z = bar x y z
  ) scope "statement"

  // succeeds if you should use a multi-line parse for this input
  val multiline: Parser[Unit] = simpleSpace.skipMany >> (
    ("table"    skip) |
    ("data"     skip) |
    ("infix"    skip) |
    ("infixr"   skip) |
    ("infixl"   skip) |
    ("prefix"   skip) |
    ("postfix"  skip) |
    ("class"    skip) |
    ("instance" skip) |
    ("private".skipOptional >> TermBindingParsers.termDef.sepBy(comma) << keyOp(":")) skip
  )

  val statements: Parser[List[Statement]] = eof.as(List()) | (for {
    s <- statement
    ss <- (semi >> statements) | (eof | virtualRightBrace).as(List())
  } yield s :: ss)

  val nakedTerm = for {
    _ <- modify(_.copy(layoutStack = List()))
    r <- term
    _ <- eof
  } yield r
}
