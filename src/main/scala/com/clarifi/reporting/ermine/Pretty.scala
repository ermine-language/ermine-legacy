package com.clarifi.reporting.ermine

import com.clarifi.reporting.{ PrimT, Header, TableName }
import com.clarifi.reporting.ermine.Type._
import com.clarifi.reporting.ermine.Kind._
import com.clarifi.reporting.ermine.Runtime.Thunk
import com.clarifi.reporting.relational.Typer._
import java.io.StringWriter
import scala.util.matching.Regex
import scala.collection.immutable.List
import scalaz.{Arrow => _, Forall => _, Name => _, _}
import scalaz.Scalaz._


/** Pretty printing for DMTL types
  *
  * @author DGP, EAK, DJD
  */

trait Pretty[+A] extends Monadic[Pretty,A] { that =>
  def self = that
  def apply(
    taken:   Set[Name],         /** Variable names that have been used */
    chosen:  Map[V[Any], Name], /** Association of 'free' variables with names */
    supply:  Seq[Local],        /** A rotating supply of suggested names */
    prec:    Int                /** The precedence level needed to leave out parentheses */
  ) : (Set[Name], Map[V[Any],Name], Seq[Local], A)

  //TODO: add a search for constructors or a list of them here
  def run: A = this(Set(), Map(), Pretty.varSupply, -1)._4
  def runAp: A = this(Set(), Map(), Pretty.varSupply, 10)._4
  def runPrec(p: Int) = this(Set(), Map(), Pretty.varSupply, p)._4

  // monadic
  def lift[B](p: Pretty[B]) = p
  def map[B](f: A => B) = new Pretty[B] {
    def apply(t: Set[Name], c: Map[V[Any],Name], s: Seq[Local], p: Int) = {
      val (tn,cn,sn,a) = that(t,c,s,p)
      (tn,cn,sn,f(a))
    }
  }
  def flatMap[B](f : A => Pretty[B]) = new Pretty[B] {
    def apply(t: Set[Name], c: Map[V[Any],Name], s: Seq[Local], p: Int) = {
      val (tn,cn,sn,x) = that(t,c,s,p)
      f(x)(tn,cn,sn,p)
    }
  }
  def when(b: Boolean) = if (b) skip
                         else Pretty(_ => ())
}
object Pretty {
  /** Suggest a name for a variable. Pulls from the infinite list of variable names we carry around. */
  def suggest : Pretty[Local] = Pretty((t,c,s,p) => (t, c, s.tail, s.head))

  import Document._

  // precedence reader
  def apply[A](f : Int => A) : Pretty[A] = new Pretty[A] {
    def apply(t: Set[Name], c: Map[V[Any],Name], s: Seq[Local], p: Int) = (t,c,s,f(p))
  }

  // full-on constructor
  def apply[A](f: (Set[Name], Map[V[Any], Name], Seq[Local], Int) => (Set[Name], Map[V[Any],Name], Seq[Local], A)): Pretty[A] = new Pretty[A] {
    def apply(t: Set[Name], c: Map[V[Any],Name], s: Seq[Local], p: Int) = f(t,c,s,p)
  }

  implicit def monad : Monad[Pretty] = new Monad[Pretty] {
    def point[A](a : => A) = new Pretty[A] {
      def apply(t: Set[Name], c: Map[V[Any],Name], s: Seq[Local], p: Int) = (t,c,s,a)
    }
    def bind[A,B](r : Pretty[A])(f : A => Pretty[B]) = r flatMap f
  }

  def scope[A](vs: List[V[Any]], act: Pretty[A]) = for {
    ns <- vs.traverse[Pretty,Name](fresh _)
    r <- act
    _ <- Pretty((t,c,s,p) => (t -- ns, c -- vs, s, ()))
  } yield r

  def ppName(n: Name): Pretty[Document] = n match {
    case Local(n,Idfix)          => unit(n)
    case Local(n,Prefix(_))      => parens(unit("prefix " + n))
    case Local(n,Postfix(_))     => parens(unit("postfix " + n))
    case Local(n,Infix(_,_))     => parens(unit(n))
    case Global(m,n,Idfix)       => unit(n) // + "_" + m)
    case Global(m,n,Prefix(_))   => parens(unit("prefix " + n)) // + "_" + m))
    case Global(m,n,Postfix(_))  => parens(unit("postfix " + n)) // + "_" + m))
    case Global(m,n,Infix(_,_))  => parens(unit(n)) // + "_" + m))
  }

  def lookupVar(v: V[Any]) : Pretty[Option[Name]] = Pretty((t,c,s,p) => (t,c,s,c get v))
  def lookupFresh(v: V[Any]): Pretty[Name] = lookupVar(v) flatMap {
    case Some(n) => n.pure[Pretty]
    case None => fresh(v)
  }
  def ppVar(v: V[Any]): Pretty[Document] = for {
    n <- lookupFresh(v)
    d <- ppName(n) map ((if(v.ty == Skolem) text("!") else empty) :: _)
  } yield d

  def unit(a : String) = new Pretty[Document] {
    def apply(t:Set[Name], c: Map[V[Any],Name], s: Seq[Local], p: Int) = (t,c,s,text(a))
  }

  class PrettyLocal(name: Local, id: Int) {
    def pretty: Local = name match {
      case _ if id == 0 => name
      case Local(n, f)  => Local(n + id.toString, f)
    }
    def bump : PrettyLocal = new PrettyLocal(name, id+1)
  }


  // This eventually generates a fresh name similar to desire on the
  // assumption that taken contains all the conflicting names.
  def generateFresh(desired: Local, taken: Set[Name]) : Name = {
    def search(cur: PrettyLocal) : PrettyLocal =
      if (taken contains cur.pretty) search(cur bump)
      else cur
    search(new PrettyLocal(desired, 0)).pretty
  }

  def fresh(v: V[Any]): Pretty[Name] = {
    def go(sug: Local): Pretty[Name] = Pretty((t,c,s,p) => {
      val name = generateFresh(sug, t)
      (t + name, c + (v -> name), s, name)
    })
    v.name match {
      case Some(sug@Local(_,_)) => go(sug)
      case Some(g) => g.pure[Pretty] // TODO: decide whether or not to show the qualifier based on if the unqualified form is taken?
      case None    => suggest flatMap (go _)
    }
  }

  // wrap a document in delimiters
  def wrap(s : String, e : String, d : Document) : Document = group(s :: d :: text(e))

  // conditionally wrap a document in delimiters
  def wrapIf(b: Boolean, l: String, r: String, d: Document) : Document = b match {
    case true  => wrap(l, r, d)
    case false => d
  }

  // Set the ambient precedence level in a given scope.
  def localPrec[A](p: Int, m: Pretty[A]) : Pretty[A] = Pretty((t,c,s,_) => m(t,c,s,p))

  // Read the ambient precedence level.
  def getPrec : Pretty[Int] = Pretty(p => p)

  // Given an operator, its precedence and associativity, and its two
  // arguments, pretty prints the overall expression with correct
  // delimiting for the ambient precedence.
  def prec(p: Int, assoc: Assoc, op: Document, l: Pretty[Document], r: Pretty[Document]): Pretty[Document] = {
    val precl = assoc match {
                  case AssocL => p
                  case AssocR => p + 1
                  case AssocN => p + 1
                }
    val precr = assoc match {
                  case AssocL => p + 1
                  case AssocR => p
                  case AssocN => p + 1
                }
    for {
      prettyl <- localPrec(precl, l)
      prettyr <- localPrec(precr, r)
      q       <- getPrec
    } yield wrapIf(q > p, "(", ")", group(prettyl :: op :: prettyr))
  }

  // Force delimiters around a particular expression
  def delimited(l: Document, r: Document, e: Pretty[Document]) : Pretty[Document] = for {
    p <- localPrec(-1, e)
  } yield (group(l :: nest(2, p) :: r))

  // scalaz could use a foldrM
  def foldrPP[A,R](xs: Traversable[A], z: R, f: (A,R) => Pretty[R]) : Pretty[R] =
    xs.foldRight(z.pure[Pretty])((x: A, r: Pretty[R]) =>
      r >>= ((y: R) => f(x, y)))

  // Prints a sep-separated collection of objects using a given pretty printing function.
  def separated[A](xs: Traversable[A], sep: Document, pp: A => Pretty[Document])
    : Pretty[Document] = {
      def reduce(x: A, m: Option[Document]): Pretty[Option[Document]] = m match {
        case None    => pp(x) map (some(_))
        case Some(d) => pp(x) map (y => some(y :: sep :: d))
      }
      foldrPP(xs, none, reduce) map (y => y getOrElse empty)
    }

  def formatRho(t: Type) : Pretty[Document] = t match {
    case ConcreteRho(_,fields) => fields.toList.traverse(n => unit(n.toString)) map (l => vcat(punctuate(text(","), l)))
    case _ => ppType(t) map (text("..") :: _)
  }

  def ppKindSchema(ks: KindSchema): Pretty[Document] = for {
    kds <- ks.forall.traverse[Pretty,Document](ppVar(_))
    p <- getPrec
    r <- localPrec(-1, ppKind(ks.body))
  } yield wrapIf(p >= 0, "(", ")", if (ks.forall.isEmpty) r else text("forall") :+: fillSep(kds) :: text(".") :+: r)

  def ppExists(xs: List[TypeVar], cs: List[Type]) = if(cs.isEmpty) empty.pure[Pretty] else
    for {
      p <- getPrec
      xds <- xs.traverse[Pretty,Document](ppTypeVarBinder(_))
      qd <- separated[Type](cs, text(",") :: line, c => localPrec(-1, ppType(c)))
    } yield wrapIf(p >= 0, "(", ")", if (xs.isEmpty) qd else text("exists") :+: fillSep(xds) :: text(".") :+: qd)

  def ppConstraints(cs: Type, t: Type): Pretty[Document] = for {
    p <- getPrec
    dcs <- localPrec(0, ppType(cs)) map { case DocNil => DocNil ; case d => d :+: text("=>") :: line }
    td <- localPrec(-1, ppType(t))
  } yield wrapIf(p >= 0, "(", ")", dcs :: nest(2, td))

  // forall {a b c} (d: a -> b) (e: c) (f: rho). (exists (g: a -> b -> c) (h: rho). f <- Foo h, Blah d g) => Bar d e f
  def ppForall(ks: List[KindVar], ts: List[TypeVar], q: Type, t: Type): Pretty[Document] = scope(ks ++ ts, for {
    kds <- ks.traverse[Pretty,Document](ppVar(_))
    tds <- ts.traverse[Pretty,Document](ppTypeVarBinder(_))
    p <- getPrec
    r <- localPrec(-1, ppConstraints(q, t))
  } yield wrapIf(p >= 0, "(", ")",
    if (ks.isEmpty && ts.isEmpty) r
    else text("forall") :+: wrapIf(kds.length > 0, "{", "} ", fillSep(kds)) :: fillSep(tds) :: text(".") :: nest(2, line :: r)
  ))

  def intersperse[A](a : A, xs : List[A]) : List[A] = xs match {
    case Nil => Nil
    case x :: Nil => x :: Nil
    case x :: xs => x :: a :: intersperse(a, xs)
  }

  // TODO: Factor out this recursion pattern, which is almost foldl1 + something
  def spaceDocs(ds : List[Document]) : Document = ds match {
    case Nil => empty
    case x :: Nil => x // Or we get an extra space
    case x :: xs => x :/: spaceDocs(xs)
  }

  def breakDocs(ds : List[Document]) : Document = ds match {
    case Nil => empty
    case x :: Nil => x
    case x :: xs => x :: break :: breakDocs(xs)
  }

  def ppTypeVarBinder(v: TypeVar): Pretty[Document] =
    for {
      d <- ppVar(v)
      k <- ppKind(v.extract)
    } yield v.extract match {
      case Star(_) => d
      case _ => "(" :: d :: text(":") :+: k :: ")"
    }

  def ppRho(m: Type): Pretty[Document] = delimited(text("(|"),text("|)"),formatRho(m))
  def braces(m: Pretty[Document]): Pretty[Document] = delimited(text("{"),text("}"), m)
  def ppRecordT(m: Type): Pretty[Document] = braces(formatRho(m))
  def ppRecord(t : Map[String, Runtime]) : Pretty[Document] = {
    def helper (t : List[(String, Runtime)], z : Document) : Pretty[Document] = t match {
      case List ((n, v)) => ppRuntime(v) map (z :: n :: " = " :: _)
      case (t, v) :: ts => for {
        x <- ppRuntime(v)
        res <- helper(ts, t :: " = " :: x :: "," :/: z)
      } yield res
      case a => monad.pure(z)
    }
    helper(t.toList, empty)
  }
  def brackets(m : Pretty[Document]): Pretty[Document] = delimited(text("["),text("]"), m)
  def parens(m : Pretty[Document]): Pretty[Document] = delimited(text("("),text(")"), m)
  def parenPrec(m: Pretty[Document]): Pretty[Document] = getPrec.flatMap(p => if (p >= 0) parens(m) else m)
  def ppRelationT(m: Type): Pretty[Document] = brackets(formatRho(m))
  def appT(e: Pretty[Document], stack: List[Type]) = stack.foldLeft(e)((b,a) => prec(10, AssocL, softline, b, ppType(a)))
  def ppAppNT(n: Name, stack: List[Type]): Pretty[Document] = (n, stack) match {
    case (Global(m,n, Prefix(p)), x::xs)     => appT(prec(p, AssocN, n :: "_" :: m :: space, unit(""), ppType(x)), xs)
    case (Global(m,n, Postfix(p)), x::xs)    => appT(prec(p, AssocN, space :: n :: "_" :: text(m), ppType(x), unit("")), xs)
    case (Global(m,n, Infix(p,a)), x::y::xs) => appT(prec(p, a, space :: n :: "_" :: m :: softline, ppType(x), ppType(y)), xs)
    case (Local(n, Prefix(p)), x::xs)     => appT(prec(p, AssocN, n :: space, unit(""), ppType(x)), xs)
    case (Local(n, Postfix(p)), x::xs)    => appT(prec(p, AssocN, space :: text(n), ppType(x), unit("")), xs)
    case (Local(n, Infix(p,a)), x::y::xs) => appT(prec(p, a, space :: n :: softline, ppType(x), ppType(y)), xs)
    case _                               => appT(ppName(n), stack)
  }
  def ppAppT(e: Type, stack: List[Type]): Pretty[Document] = (e, stack) match {
    case (Arrow(_), a::b::xs) => appT(prec(0, AssocR, space :: "->" :: line, ppType(a), ppType(b)), xs)
    case (ProductT(_,n), xs) if xs.length >= n => {
      val (l,r) = xs.splitAt(n)
      appT(parens(separated(l, text(",") :: softline, (x: Type) => localPrec(-1, ppType(x)))) , r)
    }
    case (Con(_,n,_,_), _) => ppAppNT(n, stack)
    case (VarT(v), _)      => lookupFresh(v) flatMap (n => ppAppNT(n, stack))
    case (AppT(x,y), _)    => ppAppT(x, y :: stack)
    case (x, xs)           => appT(ppType(x), xs)
  }

  def appR(e: Pretty[Document], stack: List[Runtime]) = stack.foldLeft(e)((b,a) => prec(10, AssocL, softline, b, ppRuntime(a)))
  def ppAppNR(n: Name, stack: List[Runtime]): Pretty[Document] = (n, stack) match {
    case (Local(n, Prefix(p)), x::xs)      => appR(prec(p, AssocN, n :: space, unit(""), ppRuntime(x)), xs)
    case (Local(n, Postfix(p)), x::xs)     => appR(prec(p, AssocN, space :: text(n), ppRuntime(x), unit("")), xs)
    case (Local(n, Infix(p,a)), x::y::xs)  => appR(prec(p, a, space :: n :: softline, ppRuntime(x), ppRuntime(y)), xs)
    case (Global(m,n, Prefix(p)), x::xs)     => appR(prec(p, AssocN, n :: "_" :: m :: space, unit(""), ppRuntime(x)), xs)
    case (Global(m,n, Postfix(p)), x::xs)    => appR(prec(p, AssocN, space :: n :: "_" :: text(m), ppRuntime(x), unit("")), xs)
    case (Global(m,n, Infix(p,a)), x::y::xs) => appR(prec(p, a, space :: n :: "_" :: m :: softline, ppRuntime(x), ppRuntime(y)), xs)
    case _                               => appR(ppName(n), stack)
  }

  def asList(e: Runtime, n: Int = 0): Option[(List[Runtime], Boolean)] = e.whnf match {
    case _ if n > 30 => Some((List(), true))
    case Data(Global("Builtin","Nil",Idfix),Array()) => Some((List(), false))
    case Data(Global("Builtin","::",Infix(_,_)), Array(x,xs)) => asList(xs.whnf, n + 1) map { case (xs,b) => (x :: xs, b)}
    case _ => None
  }


  def ppKind(k: Kind): Pretty[Document] = k match {
    case Rho(_)        => unit("ρ") // rho
    case Star(_)       => unit("*")
    case Field(_)      => unit("φ") // phi
    case Constraint(_) => unit("Γ") // Gamma
    case ArrowK(_,l,r) => prec(5, AssocR, space :: text("->") :: softline, ppKind(l), ppKind(r))
    case VarK(v)       => ppVar(v)
  }

  def ppType(t: Type): Pretty[Document] = t match {
    case Forall(_,ks,ts,q,t) => ppForall(ks,ts,q,t)
    case Exists(_,xs,cs)     => ppExists(xs, cs)
    case Memory(_, t)        => ppType(t)
    case ProductT(_,n)       => parens(unit("," * (n-1)))
    case VarT(v)             => ppVar(v)
    case Arrow(_)            => unit("(->)")
    case ConcreteRho(_,r)    => ppRho(t)
    case Con(_, n, _, _)     => ppName(n)
    case AppT(f, x)          => ppAppT(f, List(x)).map(group(_))
    case Part(_, l, r)       => for {
      dl <- ppType(l)
      dr <- parens(separated(r, text(",") :: line, (x: Type) => ppType(x)))
    } yield dl :+: text("<-") :+: dr
  }

  def ppRuntime(e: Runtime, d: Int = 0) : Pretty[Document] = if (d > 10) unit("...") else e match {
    case Prim(p) if p.isInstanceOf[String] => wrap("\"","\"", text(p.toString)).pure[Pretty]
    case Prim(p)     => unit(p.toString)
    case Thunk(t)    => ppRuntime(t, d + 1)
    case Rel(r)      => unit("<relation with " + extTyper(r) + ">")
    case EmptyRel    => unit("<empty relation>")
    case b@Bottom(_)   => unit("<error: " + b.thrown.getMessage + ">")
    case Rec(m)      => braces(ppRecord(m))
    case Data(Global("Builtin","Nil",Idfix),Array()) => unit("[]")
    case Data(n@Global("Builtin","::",Infix(_,_)),Array(x,xs)) => asList(xs.whnf) match {
      case Some((zs, false))  => brackets(separated(x :: zs, text(","), (x: Runtime) => localPrec(-1, ppRuntime(x, d + 1))))
      case Some((zs, true))   => brackets(separated(x :: zs, text(","), (x: Runtime) => localPrec(-1, ppRuntime(x, d + 1))) map { _ :: text("...") })
      case None      => ppAppNR(n, List(x, xs)) // Delta
    }
    case Fun(f)      => unit("<function>")
    case Data(n,arr) => ppAppNR(n, arr.toList)
    case Arr(arr)    => parens(separated(arr.toList, text(","), (x: Runtime) => localPrec(-1, ppRuntime(x, d + 1))))
  }

  def varSupply : Seq[Local] = Stream.from(0) map (i => (new PrettyLocal(Local((i % 26 + 'a'.toInt).toChar.toString,Idfix), i / 26)).pretty)

  // public API
  def prettyKind(k: Kind, p: Int = 11): Document       = ppKind(k).runPrec(p)
  def prettyType(t: Type, p: Int = 11): Document       = ppType(t).runPrec(p)
  def prettyRuntime(e: Runtime, p: Int = 11): Document = ppRuntime(e).runPrec(p)

  // fancy display
  def prettyVarHasType(v: TermVar) = (for {
    dtm <- ppVar(v)
    dty <- ppType(v.extract)
  } yield (dtm :+: text(":") :+: dty)).run

  // fancy display
  def prettyVarHasKind(v: TypeVar) = (for {
    dtm <- ppVar(v)
    dty <- ppKind(v.extract)
  } yield (dtm :+: text(":") :+: dty)).run

  def prettyTypeHasKindSchema(ty: Type, ki: KindSchema) = (for {
    dty <- ppType(ty)
    dki <- ppKindSchema(ki)
  } yield (dty :+: text(":") :+: dki)).run

  def prettyConHasKindSchema(v: Local, ks: KindSchema) = (for {
    dty <- ppName(v)
    dki <- ppKindSchema(ks)
  } yield (dty :+: text(":") :+: dki)).run

/*
  def tableDeclarations(schema: Map[TableName,Header],
                        collision: (String, PrimT, PrimT) => PrimT = (s,t1,t2) => t1): String = {
    val fields: List[(String,PrimT)] = schema.values.flatMap(a => a).toList
    val uniqueFields = fields.foldLeft(Map[String,PrimT]())((typs,nt) => {
      val (name, t2) = nt
      val entry = typs.get(name).map(t1 => (name, collision(name, t1, t2))).getOrElse((name,t2))
      typs + entry
    })
    val fieldDecls = uniqueFields.map { case (name,t) => "field %s : %s".format(name,t.name) } mkString "\n"
    val tableDecls = schema.map { case (name,cols) => "table %s : [%s]".format(name,cols.map(_._1).mkString(", ")) } mkString "\n"
    fieldDecls + "\n" + tableDecls
  }
*/
}
