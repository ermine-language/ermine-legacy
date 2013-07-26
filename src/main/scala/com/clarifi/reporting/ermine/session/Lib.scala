package com.clarifi.reporting.ermine.session

import com.clarifi.reporting._
import com.clarifi.reporting.ermine._
import com.clarifi.reporting.ermine.Subst.unfurlApp
import com.clarifi.reporting.ermine.Runtime._
import com.clarifi.reporting.ermine.Type._
import com.clarifi.reporting.ermine.Kind._
import com.clarifi.reporting.ermine.Loc.builtin
import com.clarifi.reporting.ermine.Pretty.{ ppType, ppName }
import com.clarifi.reporting.ermine.Document.{ text, nest, group }
import com.clarifi.reporting.ermine.session.Session._
import com.clarifi.reporting.Reporting._
import com.clarifi.reporting.relational.{EmptyRel => _, _}
import java.util.Date
import java.lang.Math
import scala.util.control.NonFatal
import scala.Predef.{error => _, _ }
import scalaz.{Forall => _, Arrow => _, _}
import scalaz.Scalaz._
import scala.collection.immutable.List
import sys.error
import Op._

class EmptyException extends Exception("empty")
/**
 * Library of external DMTL functions and datatypes.
 */
object Lib {
  case class DataCon(loc: Loc, name: Global, args: List[Type])

  def dataDecl(
    tyCon:        Con,
    tyConKinds:   List[KindVar],
    tyConArgs:    List[TypeVar],
    constructors: List[(Global, List[Type])]
  )(implicit s: SessionEnv, su: Supply) = {
    constructors.foreach { case (n, f) =>
      primOp(n, Runtime.accumData(n, List(), f.length),
                Forall.mk(builtin, tyConKinds, tyConArgs, Exists(builtin),
                f.foldRight(tyCon(tyConArgs.map(VarT(_)):_*))(Arrow(builtin,_,_))))
    }
    addCon(tyCon)
  }

//  private implicit def libName(s: String): Global = Global(namespace, s, Idfix)
//  private def name(s: String, f: Fixity): Global = Global(namespace, s, f)

  // @throws Death
  def addInstance(
    tyCon: Con,
    inst: Instance
  )(implicit s: SessionEnv) {
    val n = tyCon.name
    s.classes.get(n) match {
      case None    => tyCon.die("adding instance to a non-existant class")
      case Some(c) => s.classes = s.classes + (n -> (c + (inst.id -> inst)))
    }
  }

  def FA(k: Kind, f: Type => Type)(implicit su: Supply): Type = {
    val v = freshType(k)
    val b = f(VarT(v))
    val (ks,ts,q,bp) = dequantify(b)
    if (typeVars(bp).contains(v)) Forall(builtin, ks, v :: ts, q, bp)
    else if (typeVars[Type](q).contains(v)) Forall(builtin, ks, ts, Exists(builtin, List(v), List(q)), bp)
    else Forall(builtin, ks, ts, q, bp)
  }
  def FA(f: Type => Type)(implicit su: Supply): Type = FA(star,f)
  def FAR(f: Type => Type)(implicit su: Supply): Type = FA(rho,f)

  def binOp[A](n: Global, f: (A, A) => A, sig: Type)(implicit s: SessionEnv, su: Supply) = primOp(n, fun2((a,b) => Prim(f(a.extract[A],b.extract[A]))), sig ->: sig ->: sig)
  def unOp[A](n: Global, f: A => A, sig: Type)(implicit s: SessionEnv, su: Supply) = primOp(n, Fun(a => Prim(f(a.extract[A]))), sig ->: sig)

  /** Dynamically call a specific numeric function. a -> z */
  @inline final
  def numUn[Z](byte: Byte => Z, short: Short => Z, int: Int => Z,
               long: Long => Z, float: Float => Z, double: Double => Z
             )(a: AnyVal): Z = (a: @unchecked) match {
    case (a: Byte) => byte(a)
    case (a: Short) => short(a)
    case (a: Int) => int(a)
    case (a: Long) => long(a)
    case (a: Float) => float(a)
    case (a: Double) => double(a)
  }

  /** Dynamically call a generic numeric function. a -> z. */
  def numUn[Z](f: ((N, Numeric[N]) forSome {type N}) => Z
             )(a: AnyVal): Z = {
    def fi[N](a: N)(implicit ev: Numeric[N]) = f((a, ev))
    numUn(fi(_), fi(_), fi(_), fi(_), fi(_), fi(_))(a)
  }

  /** Dynamically call a specific numeric function. a -> a -> z. */
  @inline final
  def numBin[Z](byte: (Byte, Byte) => Z, short: (Short, Short) => Z,
                int: (Int, Int) => Z, long: (Long, Long) => Z,
                float: (Float, Float) => Z, double: (Double, Double) => Z
              )(a: AnyVal, b: AnyVal): Z =
    ((a, b): @unchecked) match {
      case (a: Byte, b: Byte) => byte(a, b)
      case (a: Short, b: Short) => short(a, b)
      case (a: Int, b: Int) => int(a, b)
      case (a: Long, b: Long) => long(a, b)
      case (a: Float, b: Float) => float(a, b)
      case (a: Double, b: Double) => double(a, b)
    }

  /** Dynamically call a generic numeric function. a -> a -> z. */
  def numBin[Z](f: ((N, N, Numeric[N]) forSome {type N}) => Z
              )(a: AnyVal, b: AnyVal): Z = {
    def fi[N](a: N, b: N)(implicit ev: Numeric[N]) = f((a, b, ev))
    numBin(fi(_, _), fi(_, _), fi(_, _), fi(_, _), fi(_, _), fi(_, _))(a, b)
  }

  /** Build a fun of PrimitiveNum a => a -> a.
    *
    * @param name Qualified name of the function.
    * @param f Generic numeric operation.
    * */
  def primUnOp(name: String)(f: AnyVal => Runtime): Fun =
    Fun(name, {
       case x@NullableValue(Left(_)) => x
       case NullableValue(Right(a)) => {
           Data(Global("Builtin", "Some"),
                Array(f(a.extract)))
       }
       case a => f(a.extract)})

  /** Build a fun of PrimitiveNum a => a -> a -> a.
    *
    * @param name Qualified name of the function.
    * @param f Generic numeric operation.
    * */
  def primBinOp(name: String)(f: (AnyVal, AnyVal) => Runtime): Fun =
    fun2(name, {
       case x@NullableValue(Left(_)) => {case _ => x}
       case NullableValue(Right(a)) => {
         case y@NullableValue(Left(_)) => y
         case NullableValue(Right(b)) =>
           Data(Global("Builtin", "Some"),
                Array(f(a.extract, b.extract)))
       }
       case a => {case b => f(a.extract, b.extract)}})

  def liftBool(b: Boolean): Runtime = if (b) True else False

  val list  = mkRuntimeCon(Global("Builtin","List"), star ->: star, false)
  val listH = mkCon[List[_]](Global("Native.List","List#"), star ->: star)
  val vector = mkCon[Vector[_]](Global("Vector","Vector"), star ->: star)
  val Nil = Data(Global("Builtin","Nil"))
  val prim = mkCon[PrimT](Global("Builtin","Prim"), star ->: star)
  val primExpr = mkCon[PrimExpr](Global("Prim", "PrimExpr#"), star)
  val sortOrder = mkCon[SortOrder](Global("Relation.Sort", "SortOrder#"), star)

  val maybe = mkRuntimeCon(Global("Builtin","Maybe"), star ->: star, false)
  val maybeH = mkCon[Option[_]](Global("Native.Maybe","Maybe#"), star ->: star)
  val pairH = mkCon[Tuple2[_,_]](Global("Native.Pair","Pair#"), star ->: star ->: star)
  val eitherH = mkCon[Either[_,_]](Global("Native.Either", "Either#"),
                                   star ->: star ->: star)
  val mapH = mkCon[Map[Any,Runtime]](Global("Native.Map","Map"), star ->: star ->: star)
  val primt = mkCon[PrimT](Global("Builtin","PrimT"), star)
  val Nothing = Data(Global("Builtin","Nothing"))

  val mem       = mkCon[AnyRef](Global("Builtin", "Mem"), rho ->: star)
  val smaster   = mkCon[AnyRef](Global("Builtin", "SM"), rho ->: star)
  val relationalCon: Con =
    mkClassCon(Global("Builtin", "Relational"), ((rho ->: star) ->: constraint).schema)
  val relationalCombCon: Con =
    mkClassCon(Global("Builtin", "RelationalComb"), ((rho ->: star) ->: constraint).schema)
  val numCon: Con = mkClassCon(Global("Builtin","Num"))
  val primitiveAtom = mkClassCon(Global("Builtin", "PrimitiveAtom"))
    // class Primitive a where
    //   prim: Prim a
  val eqCon = mkClassCon(Global("Builtin","Eq"))

  def mkSimpleInstance(t: Type, name: String)(implicit su: Supply) = new Instance(su.fresh) {
    def loc = Loc.builtin
    def reqs(p: List[Type]): Option[List[Type]] = p match {
      case List(`t`) => Some(List())
      case _         => None
    }
    def build(ds: List[Runtime]): Runtime = Prim(()) // no dictionary to build
    def pretty = List(("instance " + name) :+: ppType(t).runAp)
  }

  def unfurledEqInstance(c: Con, n: Int)(implicit su: Supply) = new Instance(su.fresh) {
    def loc = Loc.builtin
    def reqs(p: List[Type]): Option[List[Type]] = p match {
      case List(s) => unfurlApp(s) match {
        case Some((`c`,args)) => Some(args.map(eqCon(_)))
        case _ => None
      }
      case _ => None
    }
    def build(ds: List[Runtime]): Runtime = Prim(()) // no dictionary to build
    // assumes one argument for now, since we only ever use this with one argument
    def pretty = n match {
      case 1 => List("instance Eq (" :: ppName(c.name).runAp :+: "a" :: ")" :+: nest(4, group("|" :/: "Eq" :+: text("a"))))
      case 2 => List("instance Eq (" :: ppName(c.name).runAp :+: "a" :+: "b" :: ")" :+: nest(4, group ("|" :/: "Eq" :+: "a," :/: "Eq" :+: text("b"))))
      case _ => sys.error("TODO: rewrite unfurledEqInstance.pretty")
    }
  }

  def cons(implicit s: SessionEnv, su: Supply) =
    for(c <- List(
      Type.int, Type.long, Type.char, Type.string, Type.float, Type.double,
      Type.field, Type.byte, Type.date, Type.short, Type.ffi
    )) addCon(c)

  def simple(implicit s: SessionEnv, su: Supply) {
    freshType(star) match { case a =>
      addCon(eqCon)
      addClass(Loc.builtin, eqCon, List(a), List(), _ => List())
    }
    primOp(Global("Eq","==", InfixN(4)), fun2((a,b) => liftBool(a.extract[Any] == b.extract[Any])), FA(a => eqCon(a) =>: (a ->: a ->: bool)))
    primOp(Global("Eq","!=", InfixN(4)), fun2((a,b) => liftBool(a.extract[Any] != b.extract[Any])), FA(a => eqCon(a) =>: (a ->: a ->: bool)))
    primOp(Global("Native.Object","===", InfixN(4)), fun2((a,b) => liftBool(a.extract[AnyRef] eq b.extract[AnyRef])), FA(a => a ->: a ->: bool))
    primOp(Global("Native.Object","!==", InfixN(4)), fun2((a,b) => liftBool(a.extract[AnyRef] ne b.extract[AnyRef])), FA(a => a ->: a ->: bool))

    for (t <- List(Type.int, Type.long, Type.char, Type.string, Type.float,
                   Type.double, Type.byte, Type.date, Type.short))
      addInstance(eqCon, mkSimpleInstance(t, "Eq"))

    // the field instance
    addInstance(eqCon, new Instance(su.fresh) {
      def loc = Loc.builtin
      def reqs(p: List[Type]): Option[List[Type]] = p match {
        case List(s) => unfurlApp(s) match {
          case Some((`field`,args)) => Some(List())
          case _ => None
        }
        case _ => None
      }
      def build(ds: List[Runtime]): Runtime = Prim(()) // no dictionary to build
      // assumes one argument for now, since we only ever use this with one argument
      def pretty = List(text("instance Eq (Field (r : ρ) a)"))
    })

    // construct a magic instance that covers all products and tuples
    addInstance(eqCon, new Instance(su.fresh) {
      def loc = Loc.builtin
      def reqs(p: List[Type]): Option[List[Type]] = p match {
        case List(t) =>
          def go(t: Type, as: List[Type] = List()): Option[List[Type]] = t match {
            case AppT(f,a)    => go(f,a::as)
            case _ : ProductT => Some(as.map(eqCon(_)))
            case `recordT`     => Some(List())
            case _            => None
          }
          go(t,List())
        case _ => None
      }
      def build(ds: List[Runtime]): Runtime = Prim(())
      def pretty = List(
        text("instance Eq (a .. z) | Eq a .. Eq z"),
        text("instance Eq {..r}")
      )
    })

    // List, giving up and building it in
    dataDecl(bool, List(), List(), List(
      Global("Builtin","False") -> List(),
      Global("Builtin","True") -> List()
    ))

    addInstance(eqCon, mkSimpleInstance(bool, "Eq"))

    val listCons = Global("Builtin","::",InfixR(5))
    freshType(star) match { case a =>
      dataDecl(list, List(), List(a), List(
        Global("Builtin","Nil") -> List(),
        listCons                -> List(VarT(a),list(VarT(a)))
      ))
    }
    addInstance(eqCon,unfurledEqInstance(list,1))

    freshType(star) match { case a =>
      dataDecl(maybe, List(), List(a), List(
        Global("Builtin","Nothing") -> List(),
        Global("Builtin","Just")    -> List(VarT(a))
      ))
    }
    addInstance(eqCon,unfurledEqInstance(maybe,1))

    freshType(star) match { case a =>
      dataDecl(nullable, List(), List(a), List(
        Global("Builtin","Null") -> List(prim(VarT(a))),
        Global("Builtin","Some") -> List(VarT(a))
      ))
    }
    addInstance(eqCon,unfurledEqInstance(nullable,1))

    // Map
    // unboxes k because equality is weird on Runtimes.
    addCon(mapH)
    primOp(Global("Native.Map","insert"),
       fun3((k,v,m) => Prim(m.extract[Map[Any,Runtime]] + (k.extract[Any] -> v))),
       FA(k => FA(v => k ->: v ->: mapH(k,v) ->: mapH(k,v))))
    primOp(Global("Native.Map","empty"),
      Prim(Map[Runtime,Runtime]()),
      FA(k => FA(v => mapH(k,v))))
    primOp(Global("Native.Map","union"),
      fun2((m1, m2) => Prim(m1.extract[Map[Any,Runtime]] ++ m2.extract[Map[Any,Runtime]])),
      FA(k => FA(v => mapH(k,v) ->: mapH(k,v) ->: mapH(k,v))))
    primOp(Global("Native.Map","size"),
      Fun(m => Prim(m.extract[Map[Any,Runtime]].size)),
      FA(k => FA(v => mapH(k,v) ->: int)))
    primOp(Global("Native.Map","lookup#"),
       fun2((k,m) => Prim(m.extract[Map[Any,Runtime]].lift(k.extract[Any]))),
       FA(k => FA(v => k ->: mapH(k,v) ->: maybeH(v))))


    // Eq typeclass
    // List#
    addCon(listH)
    addInstance(eqCon,unfurledEqInstance(listH,1))
    primOp(Global("Native.List","Nil#"), Prim(List()), FA(a => listH(a)))
    primOp(Global("Native.List","::#", InfixR(5)), fun2((x,xs) => Prim(x.extract[Any] :: xs.extract[List[_]])), FA(a => a ->: listH(a) ->: listH(a)))
    primOp(Global("Native.List","head#"), Fun(xs => Prim(xs.extract[List[_]].head)), FA(a => listH(a) ->: a))
    primOp(Global("Native.List","tail#"), Fun(xs => Prim(xs.extract[List[_]].tail)), FA(a => listH(a) ->: listH(a)))
    primOp(Global("Native.List","fromList#"), Fun(xs => xs.extract[List[_]].foldRight(Nil:Runtime)((x,ys) => Data(listCons,Array(Prim(x),ys)))), FA(a => listH(a) ->: list(a)))
    primOp(Global("Native.List","mkRelation#"), Fun("Native.List.mkRelation#", {
        case Prim(l : List[Rec]) => buildRelation(l)
      }), FAR(a => listH(recordT(a)) ->: relationT(a)))
    primOp(Global("Native.List","mkMem#"), Fun("Native.List.mkMem#", {
        case Prim(l : List[Rec]) => buildMem(l)
      }), FAR(a => listH(recordT(a)) ->: mem(a)))

    // Maybe#
    addCon(maybeH)
    addInstance(eqCon,unfurledEqInstance(maybeH,1))
    primOp(Global("Native.Maybe","Nothing#"), Prim(None), FA(a => maybeH(a)))
    primOp(Global("Native.Maybe","Just#"), Fun(x => Prim(Some(x.extract[Any]))), FA(a => a ->: maybeH(a)))
    primOp(Global("Native.Maybe","fromMaybe#"), Fun("Native.Maybe.fromMaybe#", {
      case Prim(Some(a)) => Data(Global("Builtin","Just"),Array(Prim(a)))
      case Prim(None)    => Nothing
    }), FA(a => maybeH(a) ->: maybe(a)))

    // pairs
    addCon(pairH)
    addInstance(eqCon,unfurledEqInstance(pairH,2))
    primOp(Global("Native.Pair","toPair#"), Fun{ab => ab.extract[Arr] match {
          case Arr(Array(a, b)) => Prim((a.extract[Any], b.extract[Any]))
        }}, FA(a => FA(b => ProductT(builtin,2)(a,b) ->: pairH(a, b))))
    primOp(Global("Native.Pair","fst#"), Fun(x => Prim(x.extract[Tuple2[_,_]]._1)), FA(a => FA(b => pairH(a, b) ->: a)))
    primOp(Global("Native.Pair","snd#"), Fun(x => Prim(x.extract[Tuple2[_,_]]._2)), FA(a => FA(b => pairH(a, b) ->: b)))
    primOp(Global("Native.Pair","fromPair#"), Fun(x => {
        val p = x.extract[Tuple2[_,_]]
        Arr(Array(Prim(p._1),Prim(p._2)))
      }), FA(a => FA(b => pairH(a, b) ->: ProductT(builtin,2)(a, b))))

    // Either
    addCon(eitherH)

    binOp[String](Global("String", "++", InfixR(5)), _ + _, string)
    primOp(Global("String", "length"), Fun(s => Prim(s.extract[String].length)), string ->: int)
    primOp(Global("String", "split#"), fun2((s, c)=> Prim(s.extract[String].split(c.extract[Char]).toList)), string ->: Type.char ->: listH(string))

    primOp(Global("Builtin", "primLt#"), fun2((a,b) =>
      liftBool(toPrimExpr(a) < toPrimExpr(b))
    ), FA(a => a ->: a ->: bool))

    primOp(Global("Builtin", "primLte#"), fun2((a,b) =>
      liftBool(toPrimExpr(a) <= toPrimExpr(b))
    ), FA(a => a ->: a ->: bool))

    primOp(Global("Builtin", "primGt#"), fun2((a,b) =>
      liftBool(toPrimExpr(a) > toPrimExpr(b))
    ), FA(a => a ->: a ->: bool))

    primOp(Global("Builtin", "primGte#"), fun2((a,b) =>
      liftBool(toPrimExpr(a) >= toPrimExpr(b))
    ), FA(a => a ->: a ->: bool))

    primOp(Global("Builtin", "primPlus#"), primBinOp("Builtin.primPlus#")(numBin{
      case (a, b, num) => Prim(num plus (a, b))}), FA(a => a ->: a ->: a))

    primOp(Global("Builtin", "primMinus#"), primBinOp("Builtin.primMinus#")(numBin{
      case (a, b, num) => Prim(num minus (a, b))}), FA(a => a ->: a ->: a))

    primOp(Global("Builtin", "primTimes#"), primBinOp("Builtin.primTimes#")(numBin{
      case (a, b, num) => Prim(num times (a, b))}), FA(a => a ->: a ->: a))

    primOp(Global("Builtin", "primDiv#"),
           primBinOp("Builtin.primDiv#"){(a, b) =>
             Prim(numBin((_ / _), (_ / _), (_ / _),
                         (_ / _), (_ / _), (_ / _))(a, b))},
           FA(a => a ->: a ->: a))

    primOp(Global("Builtin", "primMod#"),
           primBinOp("Builtin.primMod#"){(a, b) =>
             Prim(numBin((_ % _), (_ % _), (_ % _),
                         (_ % _), (_ % _), (_ % _))(a, b))},
           FA(a => a ->: a ->: a))

    primOp(Global("Builtin", "primToInt#"), Fun(a =>
      Prim(numUn{case (a, num) => num toInt a}(a.extract))), FA(a => a ->: int))

    primOp(Global("Builtin", "primToDouble#"), Fun(a =>
      Prim(numUn{case (a, num) => num toDouble a}(a.extract))), FA(a => a ->: double))

    primOp(Global("Builtin", "primToLong#"), Fun(a =>
      Prim(numUn{case (a, num) => num toLong a}(a.extract))), FA(a => a ->: long))

    primOp(Global("Builtin", "primNeg"), primUnOp("Builtin.primNeg")(numUn{
      case (a, num) => Prim(num negate a)}), FA(a => numCon(a) =>: a ->: a))

    primOp(Global("Builtin", "primNeg#"), primUnOp("Builtin.primNeg#")(numUn{
      case (a, num) => Prim(num negate a)}), FA(a => a ->: a))

    primOp(Global("Builtin", "primAbs#"), primUnOp("Builtin.primAbs#")(numUn{
      case (a, num) => Prim(num abs a)}), FA(a => a ->: a))

    primOp(Global("Builtin", "primPow#"), primBinOp("Builtin.primPow#")((a,b) =>
             Prim(numBin((a: Byte, b) => math.pow(a, b).toByte,
                         (a: Short, b) => math.pow(a, b).toShort,
                         (a: Int, b) => math.pow(a, b).toInt,
                         (a: Long, b) => math.pow(a, b).toLong,
                         (a: Float, b) => math.pow(a, b).toFloat,
                         (a: Double, b) => math.pow(a, b))(a, b))),
           FA(a => a ->: a ->: a))

    // equality
    primOp(Global("Native.Object","isNull"), Fun("Native.Object.isNull",
      { case Prim(null) => True
        case _          => False
      }), FA(a => a ->: bool))
    primOp(Global("Double","epsilon"), Prim(Double.MinPositiveValue), double)
    primOp(Global("Float","epsilon"), Prim(Float.MinPositiveValue), float)
  }

  // Ops
  val relOp = mkCon[Op](Global("Relation.Op.Type", "Op"), rho ->: star ->: star)

  // Predicates
  val predicate = mkCon[Predicate](Global("Builtin","Predicate"), rho ->: star)

  def mkBinPred(op: Global, comb: (=> Predicate, => Predicate) => Predicate)(implicit s: SessionEnv, su: Supply) =
    primOp(op, fun2(op.toString, { case Prim(p) => { case Prim(q) => Prim(comb(p.asInstanceOf[Predicate], q.asInstanceOf[Predicate]))}}),
      FA(d => FA(e => FA(f => FA(a => FA(b => FA(c =>
        List(d -> List(a,b), e -> List(b,c), f -> List(a,b,c)) =>: predicate(d) ->: predicate(e) ->: predicate(f))))))))

  def relations(implicit s: SessionEnv, su: Supply) {
    primOp(Global("Field","cons"), fieldFun(s => Fun(v => Fun("Field.cons", { case Rec(m) => Rec(m + (s -> v))}))),
      FAR(r => FA(a => FAR(s => FAR(t => (t -> List(r,s)) =>: field(r, a) ->: a ->: recordT(s) ->: recordT(t))))))
    primOp(Global("Field","!", InfixR(5)), Fun(e => fieldFun(s => e.whnfMatch("!") { case Rec(m) => m(s) })),
      FAR(t => FAR(r => FA(a => FAR(s => (t -> List(r,s)) =>: recordT(t) ->: field(r, a) ->: a)))))
    primOp(Global("Field","\\", InfixR(5)), Fun(e => fieldFun(s => e.whnfMatch("\\") { case Rec(m) => Rec(m - s) })),
      FAR(t => FAR(r => FA(a => FAR(s => (t -> List(r,s)) =>: recordT(t) ->: field(r, a) ->: recordT(s))))))
    primOp(Global("Field","fieldName"), fieldFun(Prim(_)), FAR(r => FA(a => field(r, a) ->: string)))

    // The type of in-memory relations
    addCon(mem)
    // The type of security Master data
    addCon(smaster)

    primOp(Global("Field","existentialF#"), fun2("Field.existentialF", {
      case Prim(s:String) => { case p@Prim(t: PrimT) =>
        Data(Global("Field", s), Array(p))
      }}), FAR(r => FA(a => string ->: prim(a) ->: field(r,a))))

    addCon(primt)

    addCon(predicate)

    primOp(Global("Field", "fieldType"),
           fieldTup((n, t) => Prim(t)),
           FAR(r => FA(a => field(r, a) ->: prim(a))))

    // Relational constructor, type class
    freshType(rho ->: star) match {
      case a =>
        addCon(relationalCon)
        addClass(Loc.builtin, relationalCon, List(a), List(), _ => List())
    }

    // class RelationalComb (rel: ρ -> * -> *) | Relational rel
    {
      val rel = freshType(rho ->: star)
      addCon(relationalCombCon)
      addClass(Loc.builtin, relationalCombCon, List(rel),
               List(relationalCon(VarT(rel))), List(_))
    }

    for (r <- List(mem, relationT, smaster))
      addInstance(relationalCon, mkSimpleInstance(r, "Relational"))

    for (r <- List(mem, relationT))
      addInstance(relationalCombCon, mkSimpleInstance(r, "RelationalComb"))

    // Predicates
    primOp(Global("Relation.Predicate","filter"), fun2("Relation.Predicate.filter", { case Prim(p: Predicate) => {
      case Rel(e) => Rel(FilterE(e, p))
      case EmptyRel => EmptyRel}}),
      FA(rho ->: star, rel => FAR(a => FAR(t => FAR(r =>
        (t -> List(a,r)) =>: relationalCombCon(rel) =>:
        predicate(a) ->: rel(t) ->: rel(t))))))

    val emptyRho = ConcreteRho(builtin,Set())

    addCon(sortOrder)
    primOp(Global("Relation.Sort","limit#"), fun4("limit#", { case Prim(lop: List[(String, SortOrder)]) => { case Prim(lo: Option[Int]) => { case Prim(hi: Option[Int]) => {
        case EmptyRel => EmptyRel
        case Rel(ExtRel(r, db)) => Rel(ExtRel(Limit(r,lo,hi,lop), db))}}}}),
        FAR(r => listH(pairH(string,sortOrder)) ->: maybeH(int) ->: maybeH(int) ->: relationT(r) ->: relationT(r)))

    primOp(Global("Relation.Row","project#"), fun2("Relation.Row.project#", {
      case Prim(h: List[(String, PrimT)]) => {
        case Rel(r) => Rel(ProjectE(r, headerProj(h.toMap)))
        case EmptyRel => EmptyRel}}),
      FA(rho ->: star, rel => FAR(r => FAR(t => FAR(s =>
        (t -> List(r,s)) =>: relationalCombCon(rel) =>:
        listH(pairH(string, primt)) ->: rel(t) ->: rel(r))))))

    primOp(Global("Relation.Row","except#"), fun2("Relation.Row.except#", {
      case Prim(h: List[(String, PrimT)]) => {
        case Rel(r) => Rel(ExceptE(r, h.toMap.keySet))
        case EmptyRel => EmptyRel}}),
      FA(rho ->: star, rel => FAR(r => FAR(t => FAR(s =>
        (t -> List(r,s)) =>: relationalCombCon(rel) =>:
        listH(pairH(string, primt)) ->: rel(t) ->: rel(s))))))

    primOp(Global("Relation","rename"), fun3("Relation.rename", { case Data(x, tx) => { case Data(y, ty) => {
      case Rel(r) =>
        Rel(RenameE(r, Attribute(x.string, tx(0).extract[PrimT]), y.string))
      case EmptyRel => EmptyRel}}}),
      FAR(r1 => FA(a => FAR(r2 => FA(rho ->: star, rel => FAR(u1 => FAR(u2 => FAR(t =>
        List(u1 -> List(r1,t), u2 -> List(r2,t)) =>: relationalCombCon(rel) =>:
        field(r1, a) ->: field(r2, a) ->: rel(u1) ->: rel(u2)))))))))

    primOp(
      Global("Relation", "promote"),
      fun3("Relation.promote", { case Data(x, tx) => { case Data(y, ty) => {
        case Rel(ExtMem(m)) =>
          Rel(ExtMem(RenameM(m, Attribute(x.string, tx(0).extract[PrimT]), y.string, true)))
        case EmptyRel => EmptyRel
      }}}),
      FAR(r1 => FA(a => FAR(r2 => FAR(u1 => FAR(u2 => FAR(t =>
        List(u1 -> List(r1, t), u2 -> List(r2, t)) =>: primitiveAtom(a) =>:
        field(r1, a) ->: field(r2, nullable(a)) ->: mem(u1) ->: mem(u2))))))))

    primOp(Global("Relation.Row","projectT#"), fun2("Relation.Row.project#", { case Prim(h) => {
      case Rec(r) =>
        val ks = h.asInstanceOf[List[String]].toSet
        Rec(r.filterKeys(ks(_)))
      }}),
      FAR(r => FAR(t => FAR(s => (t -> List(r,s)) =>: listH(string) ->: recordT(t) ->: recordT(r)))))
    primOp(Global("Relation.Row","exceptT#"), fun2("Relation.Row.except#", { case Prim(h) => {
        case Rec(r) => Rec(r -- h.asInstanceOf[List[String]].toSet)
      }}),
      FAR(r => FAR(t => FAR(s => (t -> List(r,s)) =>: listH(string) ->: recordT(t) ->: recordT(s)))))

    val aggregate = addCon(mkCon[AggFunc](Global("Relation.Aggregate.Type", "Aggregate"), rho ->: star ->: star))

    primOp(Global("Relation.Aggregate", "aggregate"), fun3("Relation.Aggregate.aggregate", {
        case aggFun => {
          case Data(n, arr) => {
            case EmptyRel => EmptyRel
            case Rel(r) =>
              Rel(AggregateE(r, Attribute(n.string,arr(0).extract),aggFun.extract[AggFunc]))
          }
        }
      }),
      FAR(r => FA(a => FA(rho ->: star, rel => FAR(f => FAR(s => FAR(u =>
        List(s -> List(r, u)) =>: relationalCombCon(rel) =>:
          aggregate(r, a) ->: field(f, a) ->: rel(s) ->: rel(f))))))))

    primOp(Global("Relation","memoRel"), Fun("Relation.memoRel", {
          case Rel(r) => Rel(MemoE(r))
          case EmptyRel => EmptyRel
        }),
      FAR(z => FA(rho ->: star, rel => relationalCombCon(rel) =>: rel(z) ->: rel(z))))

    primOp(Global("Relation","join"), fun2("Relation.join", {
      case EmptyRel => { case EmptyRel|Rel(_) => EmptyRel }
      case Rel(r1) => {
        case EmptyRel => EmptyRel
        case Rel(r2) => // if db1 == db2 =>
          Rel(JoinE(r1, r2))
        //case Rel(ExtRel(r2, db2)) => sys.error("Can't join. " + db1 + " and " + db2 + " are not the same.")
      }}),
      FA(rho ->: star, rel => FAR(d => FAR(e => FAR(f => FAR(a => FAR(b => FAR(c =>
        List(d -> List(a,b), e -> List(b,c), f -> List(a,b,c)) =>:
        relationalCombCon(rel) =>:
        rel(d) ->: rel(e) ->: rel(f)))))))))

    def mkJoin(fn: String, j: (Mem[Nothing, Nothing], Mem[Nothing, Nothing]) => Mem[Nothing, Nothing]) =
      primOp(Global("Relation", fn), fun2("Relation." + fn, {
        case EmptyRel => { case EmptyRel|Rel(_) => EmptyRel }
        case Rel(ExtMem(r1)) => {
          case EmptyRel => EmptyRel
          case Rel(ExtMem(r2)) => Rel(ExtMem(j(r1,r2)))
        }}),
        FAR(d => FAR(e => FAR(f => FAR(a => FAR(b => FAR(c => List(d -> List(a,b), e -> List(b,c), f -> List(a,b,c)) =>:
          mem(d) ->: mem(e) ->: mem(f))))))))

    mkJoin("hashJoin", HashInnerJoin(_, _))
    mkJoin("mergeJoin", MergeOuterJoin(_, _))

    primOp(
      Global("Relation", "hashLeftJoin"),
      fun3("Relation.hashLeftJoin", { case _ => {
          case EmptyRel => { case  EmptyRel|Rel(_) => EmptyRel }
          case r@Rel(ExtMem(inner)) => {
            case EmptyRel           => r
            case Rel(ExtMem(outer)) => Rel(ExtMem(HashLeftJoin(inner, outer)))
          }
        }
      }),
      FAR(extra => FA(a => FAR(r1 => FAR(r2 => FAR(r3 => FAR(s => FAR(t =>
        List(r1 -> List(s,t), r2 -> List(t, extra), r3 -> List(s, t, extra)) =>:
        field(extra, nullable(a)) ->: mem(r1) ->: mem(r2) ->: mem(r3))))))))
    )

    val unifyFields = addCon(mkCon[List[(String,String)]](Global("Relation.UnifyFields","UnifyFields"), rho ->: rho ->: star))
    primOp(Global("Relation.UnifyFields","unifyEmpty"), Prim(List[(String, String)]()), unifyFields(emptyRho,emptyRho))
    primOp(Global("Relation.UnifyFields","unifyCons"), fieldFun(f => fieldFun(g => Fun("Relation.UnifyFields.unifyCons", { case Prim(xs: List[(String, String)]) => Prim((f,g)::xs) }))),
      FAR(r1 => FA(a => FAR(r2 => FAR(r3 => FAR(r4 => FAR(r13 => FAR(r24 => List(r13 -> List(r1,r3), r24 -> List(r2,r4)) =>:
        field(r1,a) ->: field(r2,a) ->: unifyFields(r3,r4) ->: unifyFields(r13,r24)))))))))
    primOp(Global("Relation.UnifyFields", "joinOn"), fun3("Relation.UnifyFields.joinOn", { case Prim(uf) => {
      case EmptyRel => { case EmptyRel|Rel(_) => EmptyRel }
      case Rel(ExtRel(r1, db1)) => {
        case EmptyRel => EmptyRel
        case Rel(ExtRel(r2, db2)) if db1 == db2 =>
          Rel(ExtRel(JoinOn(r1,r2,uf.asInstanceOf[List[(String, String)]].toSet), db1))
        case Rel(ExtRel(r2, db2)) => sys.error("Can't join. " + db1 + " and " + db2 + " are not the same.")
      }}}),
        FAR(r1 => FAR(r2 => FAR(s1 => FAR(s2 => FAR(s3 => FAR(a => FAR(b => FAR(c => FAR(t1 => FAR(t2 =>
          List(r1 -> List(a,b),
               r2 -> List(b,c),
               s1 -> List(r1,t1),
               s2 -> List(r2,t2),
               s3 -> List(s1,t2,c)
          ) =>: unifyFields(r1,r2) ->: relationT(s1) ->: relationT(s2) ->: relationT(s3))))))))))))

    primOp(Global("Relation","union"), fun2("Relation.union", {
      case EmptyRel => {
        case EmptyRel => EmptyRel
        case rr2@Rel(_) => rr2
      }
      case rr1@Rel(ExtRel(r1, db1)) => {
        case EmptyRel => rr1
        case Rel(ExtRel(r2, db2)) /*TODO SMRC if db1 == db2*/ => Rel(ExtRel(Union(r1, r2), db1))
        /*case Rel(ExtRel(r2, db2)) =>
          sys.error("Can't union. " + db1 + " and " + db2 + " are not the same.")*/
      }
    }), FAR(r => relationT(r) ->: relationT(r) ->: relationT(r)))

    primOp(Global("Relation","difference"), fun2("Relation.difference", {
      case EmptyRel => { case EmptyRel|Rel(_) => EmptyRel }
      case rr1@Rel(ExtRel(r1, db1)) => {
        case EmptyRel => rr1
        case Rel(ExtRel(r2, db2)) if db1 == db2 => Rel(ExtRel(Minus(r1, r2), db1))
        case Rel(ExtRel(r2, db2)) =>
          sys.error("Can't diff. " + db1 + " and " + db2 + " are not the same.")
      }
    }), FAR(r => relationT(r) ->: relationT(r) ->: relationT(r)))

    addCon(relOp)
    val unsafeOp = addCon(mkCon[Op](Global("Relation.Op.Unsafe", "Op#"), star))
    asOp

    primOp(Global("Relation.Op.Unsafe", "combine#"), fun3("Relation.Op.Unsafe", {
      case Data(frid, Array(pt)) => {
        case Prim(colval: Op) => {
          case er@EmptyRel => er
          case Rel(r) => Rel(CombineE(r, Attribute(frid.string, pt.extract[PrimT]), colval))
     }}}), FAR(r => FA(a => FA(rho ->: star, rel => FAR(s => FAR(t => relationalCombCon(rel) =>:
              field(r, a) ->: unsafeOp ->: rel(s) ->: rel(t)))))))

    // error: "erroneous or inaccesable type".  Replace classmanifest with classtag.
    val rel: Con = addCon(mkCon[ClosedExt](Global("Native.Relation","Relation#")))

    primOp(Global("Relation", "header#"), Fun("Relation.header#", {
      case Prim(rel: ClosedExt) => Prim(rel.header.toList: List[(String, PrimT)])
    }), rel ->: listH(pairH(string, primt)))

    primOp(Global("Relation", "asMem"), Fun("Relation.asMem", {
      case t@EmptyRel => t
      case t@Rel(ExtMem(_)) => t
      case Rel(e) => Rel(ExtMem(EmbedMem(e)))
    }), FA(rho ->: star, rel => FAR(a => relationalCon(rel) =>: rel(a) ->: mem(a))))

    def storedFunctionish(name: String,
                          f: (String, String, List[String],
                              OrderedHeader,
                              List[Either[(String, Ext[Nothing, Nothing]), PrimExpr]])
                           => Ext[Nothing, Nothing]): Runtime =
      fun3(name, {
             case Prim(dbc: String) => {
               case Prim(proc: String) => {
                 case Prim(qual: List[String]) =>
                   fun2(name, {
                          case Prim(rowty: OrderedHeader) => {
                            case Prim(args: List[Either[(String, Ext[Nothing, Nothing]),
                                                        PrimExpr]]) =>
                              Rel(f(dbc, proc, qual, rowty, args))}})}}})

    primOp(Global("Syntax.Procedure", "unsafeCallStoredProcedure#"),
           storedFunctionish("Syntax.Procedure.unsafeCallStoredProcedure#",
                             {(dbc, proc, qual, rowty, args) =>
             val usableArgs = TableProc.relFunctor(args map \/.fromEither){
               case ExtRel(r, _) /* if dbc matches? see join */ => r
               case _ =>
                 sys error "unimportable stored procedure argument"
             }
             ExtRel(TableProc(usableArgs, rowty, proc, qual), dbc)}),
           FAR(r => FAR(sk => string ->: string ->: listH(string)
                 ->: listH(pairH(string, primt))
                 ->: listH(eitherH(pairH(string, relationT(sk)), primExpr))
                 ->: relationT(r))))

    primOp(Global("Native.Relation","relation#"), Fun(x => x.whnfMatch("Native.Relation.relation#") {
             case EmptyRel => Prim(Closed(ExtMem(relational.EmptyRel(Map())), Map()))
             case Rel(e) => Prim(Typer.closedExt(Optimizer.optimize(e)))
           }),
           FA(rho ->: star, r => FAR(a => relationalCon(r) =>: r(a) ->: rel)))

    primOp(Global("Native.Relation", "letR"), fun2((x, f) => {
      val ext: Option[Ext[Nothing, Nothing]] = x.whnf match {
        case EmptyRel => Some(ExtMem(relational.EmptyRel(Map())))
        case Rel(e) => Some(e)
        case _ => None
      }
      val unique = new Object
      f.whnfMatch("Native.Relation.letR") {
        case Fun(g) => g(Rel(ExtRel(QuoteR(unique), ""))).whnfMatch("Native.Relation.letR") {
          case EmptyRel => EmptyRel
          case Rel(ExtRel(r, db)) => ext map (v => Rel(ExtRel(LetR(v, r.unquoteR(x =>
            if (x eq unique) Some(VarR(RTop)) else None)), db))) getOrElse
              Bottom(throw new RuntimeException("Expected a relation in a bound variable: Native.Relation.letR"))
        }
      }
    }), FA(rho ->: star, r => FAR(a => FAR(b =>
            relationalCon(r) =>: r(a) ->: (relationT(a) ->: relationT(b)) ->: relationT(b)))))

    primOp(Global("Native.Relation", "letM"), fun2((x, f) => {
      val ext: Option[Ext[Nothing, Nothing]] = x.whnf match {
        case EmptyRel => Some(ExtMem(relational.EmptyRel(Map())))
        case Rel(e) => Some(e)
        case _ => None
      }
      val unique = new Object
      f.whnfMatch("Native.Relation.letM") {
        case Fun(g) => g(Rel(ExtMem(QuoteMem(unique)))).whnfMatch("Native.Relation.letM") {
          case EmptyRel => EmptyRel
          case Rel(ExtMem(r)) => ext map (v => Rel(ExtMem(LetM(v, r.unquoteM(x =>
            if (x eq unique) Some(VarM(MTop)) else None))))) getOrElse
              Bottom(throw new RuntimeException("Expected a relation in a bound variable: Native.Relation.letM"))
        }
      }
    }), FA(rho ->: star, r => FAR(a => FAR(b =>
            relationalCon(r) =>: r(a) ->: (mem(a) ->: mem(b)) ->: mem(b)))))

    primOp(Global("Relation.Row", "groupBy#"), fun3((k, f, rel) => {
      val ext: Option[Mem[Nothing, Nothing]] = rel.whnf match {
        case EmptyRel => Some(relational.EmptyRel(Map()))
        case Rel(ExtMem(e)) => Some(e)
        case _ => None
      }
      val key = k.whnf match {
        case Prim(h: List[(String, PrimT)]) => h.map(p => Attribute(p._1, p._2))
        case _ => throw new RuntimeException("groupBy# first argument not a List[(String,PrimT)]: " + k)
      }
      val h = new Object
      val unique = new Object { override def toString = "groupBy-quote:"+h }
      f.whnfMatch("Relation.Row.groupBy#") {
        case Fun(g) => g(Rel(ExtMem(QuoteMem(unique)))).whnfMatch("Relation.Row.groupBy#") {
          case EmptyRel => EmptyRel
          case Rel(ExtMem(r)) => ext map (v => Rel(ExtMem(GroupByM(v, key, r.unquoteM(x =>
            if (x eq unique) Some(VarM(MTop)) else None))))) getOrElse
              Bottom(throw new RuntimeException("Expected a relation in a bound variable: Native.Relation.groupBy#"))
        }
      }
    }), FAR(v => FAR(v2 => FAR(kv => FAR(kv2 =>
            listH(pairH(string, primt)) ->: (mem(v) ->: mem(v2)) ->: mem(kv) ->: mem(kv2))))))


    val scanner = mkCon[Scanner[Any]](Global("Scanners","Scanner"), (star ->: star) ->: star)
    primOp(Global("Native.Relation", "runRelation"), fun2((scanner,rel) => {
      scanner.whnfMatch("Native.Relation.runRelation") {
        case Prim(s) if s.isInstanceOf[Scanner[Any]] =>
          type f[x] = Int => x
          val S = s.asInstanceOf[Scanner[f]] // `f` is an arbitrary concrete type ctor
                                             // we are really polymorphic in this ctor,
                                             // and use only the functor instance S.M
          rel.whnfMatch("Native.Relation.runRelation") {
            case Rel(r) => Prim { S.M.map(S.collect(r)) { rows =>
              rows map (rec => Rec(rec.mapValues(v => Prim(v))))
            }}
          }
        }
      }
    ), FA(star ->: star, f => FA(rho ->: star,
         (r:Type) => FAR(a => relationalCon(r) =>: scanner(f) ->: r(a) ->: f(vector(recordT(a)))))))

    primOp(Global("Native.Relation", "accumulate"), fun5((pid,nid, f, l, t) => {
      val (parentId, pTyp) = pid.whnf match {
        case Data(Global(_,n,_), ts) => (n, ts(0).extract[PrimT])
        case _ => sys.error("unpossible")
      }
      val (nodeId, nTyp) = nid.whnf match {
        case Data(Global(_,n,_), ts) => (n, ts(0).extract[PrimT])
        case _ => sys.error("unpossible")
      }
      val leaves: Option[Mem[Nothing, Nothing]] = l.whnf match {
        case EmptyRel => Some(relational.EmptyRel(Map()))
        case Rel(ExtMem(e)) => Some(e)
        case _ => None
      }
      val tree: Option[Mem[Nothing, Nothing]] = t.whnf match {
        case EmptyRel => Some(relational.EmptyRel(Map()))
        case Rel(ExtMem(e)) => Some(e)
        case _ => None
      }
      val unique = new Object
      f.whnfMatch("Native.Relation.accumulate") {
        case Fun(g) => g(Rel(ExtMem(QuoteMem(unique)))).whnfMatch("Native.Relation.accumulate") {
          case EmptyRel => EmptyRel
          case Rel(ExtMem(r)) => (for {
            lvs <- leaves
            tre <- tree
          } yield Rel(ExtMem(AccumulateM(
            Attribute(parentId, pTyp),
            Attribute(nodeId, nTyp),
            r.unquoteM(x => if (x eq unique) Some(VarM(MTop)) else None),
            lvs, tre)))
          ) getOrElse (Bottom(throw new RuntimeException("Expected a relation in a bound variable: Native.Relation.accumulate")))
        }
      }
    }), FAR(pid => FAR(nid => FA(id => FAR(v => FAR(v2 => FAR(k => FAR(nidv => FAR(nidv2 => FAR(pidnidk =>
          List(nidv -> List(nid,v), nidv2 -> List(nid,v2), pidnidk -> List(pid,nid,k)) =>:
          field(pid, id) ->:
          field(nid, id) ->:
          (mem(v) ->: mem(v2)) ->:
          mem(nidv) ->:
          mem(pidnidk) ->: mem(nidv2)))))))))))

    val rec = addCon(mkCon[Map[String,Runtime]](Global("Native.Record","Record#")))
    val scalaRec = addCon(mkCon[Record](Global("Native.Record", "ScalaRecord#")))
    primOp(Global("Native.Record","record#"), Fun(x => x.whnfMatch("Native.Record.record#") {
           case t@Rec(m) =>
             try { Prim(m.mapValues(_.whnf)) }
             catch { case NonFatal(e) => Bottom(throw new RuntimeException("error invoking record#", e)) }
         }), FAR(a => recordT(a) ->: rec))
    primOp(Global("Native.Record","unsafeRecordIn#"), Fun(x => x.whnfMatch("Native.Record.unsafeRecordIn#") {
           case Prim(p) => Rec(p.asInstanceOf[Map[String,Runtime]]) }
         ), FAR(a => rec ->: recordT(a)))
    primOp(Global("Native.Record","appendRec#")
                 , Fun( x => x.whnfMatch("Native.Record.appendRec#") {
                   case t@Rec(m) =>
                     try {  Fun(y => y.whnfMatch("Native.Record.appendRec#") {
                              case t2@Rec(m2) =>
                                 try { Rec(m ++ m2) }
                                 catch { case NonFatal(e) => Bottom(throw new RuntimeException("error invoking appendRec#", e)) }})
                         }
                     catch { case NonFatal(e) => Bottom(throw new RuntimeException("error invoking appendRec#", e)) }
                 })
                 , FAR(a => FAR(b => FAR(c => recordT(a) ->: recordT(b) ->: recordT(c)))))
    primOp(Global("Native.Record", "scalaRecord#"),
           Fun(x => x.whnfMatch("Native.Record.scalaRecord#") {
             case Prim(t: Map[String, Runtime]) => Prim(t mapValues (toPrimExpr(_)))
           }),
           rec ->: scalaRec)
    primOp(Global("Native.Record", "scalaRecordIn#"),
           Fun(x => x.whnfMatch("Native.Record.scalaRecordIn#") {
             case Prim(t: Record) => Prim(t mapValues (fromPrimExpr(_)))
           }),
           scalaRec ->: rec)

    import backends.DB

    val dbCon = addCon(mkCon[DB[Any]](Global("DB", "DB"), star ->: star))
  }

  private def asOp(implicit s: SessionEnv, su: Supply) {
    val opMod = "Relation.Op"
    val opKind = rho ->: star ->: star
    // class AsOp (a: ρ -> * -> *)
    val asOpCon = mkClassCon(Global(opMod, "AsOp"),
                             (opKind ->: constraint).schema)
    addCon(asOpCon)
    freshType(opKind) match {case cargs =>
      addClass(Loc.builtin, asOpCon, List(cargs), List(), _ => List())
    }
    // AsOp instances
    for (rssTy <- Vector(relOp, Type.field))
      addInstance(asOpCon, new Instance(su.fresh) {
        def loc = Loc.builtin
        def reqs(p: List[Type]): Option[List[Type]] = p match {
          case List(s) => unfurlApp(s) match {
            case Some((`rssTy`,args)) => Some(List())
            case _ => None
          }
          case _ => None
        }
        def build(ds: List[Runtime]): Runtime = Prim(()) // no dictionary to build
        // assumes one argument for now, since we only ever use this with one argument
        def pretty = List("instance Op" :+: Pretty.prettyType(rssTy))
      })
    // asOp : AsOp o => o r a -> Op r a
    primOp(Global(opMod, "asOp"), Fun(x =>
      x.whnfMatch(opMod + ".asOp") {
        case Data(frid, Array(pt)) =>    // Field
          Prim(Op.ColumnValue(frid.string, pt.extract))
        case x@Prim(_: Op) => x}),
          FA(opKind,
             o => FAR(r => FA(a => asOpCon(o) =>: o(r, a) ->: relOp(r, a)))))
  }

  /** Builtin bindings of `Prim *` values.  */
  val primBindings: Iterable[(Global, PrimT, Type, Boolean /* scaled? */)] =
    Vector((Global("Prim","Int"),    PrimT.IntT(true),      prim(int),    true),
           (Global("Prim","String"), PrimT.StringT(0,true), prim(string), false),
           // (Global("Prim","Float"),  PrimT.FloatT(true),    prim(float),  true)
           (Global("Prim","Bool"),   PrimT.BooleanT(true),  prim(bool),   false),
           // (Global("Prim","Uuid"),   PrimT.UuidT(true),     prim(uuid),   false)
           (Global("Prim","Double"), PrimT.DoubleT(true),   prim(double), true),
           (Global("Prim","Byte"),   PrimT.ByteT(true),     prim(byte),   true),
           (Global("Prim","Short"),  PrimT.ShortT(true),    prim(short),  true),
           (Global("Prim","Long"),   PrimT.LongT(true),     prim(long),   true),
           (Global("Prim","Date"),   PrimT.DateT(true),     prim(date),   true))

  def prims(implicit s: SessionEnv, su: Supply) {
    addCon(prim)
    for (b <- primBindings; (name, primt, typ, _) = b)
      primOp(name, Prim(primt), typ)

    def primInstance(cls: Con, t: Type, d: PrimT) = new Instance(su.fresh) {
      def loc = Loc.builtin
      def reqs(p: List[Type]): Option[List[Type]] = p match {
        case List(`t`) => Some(List())
        case _         => None
      }
      def build(ds: List[Runtime]): Runtime = Prim(d)
      def pp = for {
        tDoc <- ppType(AppT(cls,t))
      } yield "instance" :+: tDoc
      def pretty = List(pp.run)
    }

    // class Primitive a where
    //   prim: Prim a
    val primitive = {
      val a = freshType(star)
      val con = addCon(mkClassCon(Global("Builtin","Primitive")))
      addClass(Loc.builtin, con, List(a), List(), _ => List())
    }

    for ((t,d) <- primTypes) {
      addInstance(primitive, primInstance(primitive,t,d))
      addInstance(primitive, primInstance(primitive, nullable(t), d.withNull))
    }

    // class Scaled a
    val scaled = {
      val a = freshType(star)
      addClass(Loc.builtin, addCon(mkClassCon(Global("Builtin","Scaled"))),
               List(a), List(), List(_))
    }

    // class PrimitiveNum a | Primitive a, Scaled a
    val primitiveNum = {
      val a = freshType(star)
      val con = addCon(mkClassCon(Global("Builtin","PrimitiveNum")))
      addClass(Loc.builtin, con, List(a), List(primitive(VarT(a)), scaled(VarT(a))), List(_))
    }

    for ((t,d) <- primNumTypes) {
      addInstance(primitiveNum, primInstance(primitiveNum,t,d))
      addInstance(primitiveNum, primInstance(primitiveNum, nullable(t), d.withNull))
    }

    // class PrimitiveAtom a | Primitive a where
    //   nullable :: Prim (Nullable a)
    {
      val a = freshType(star)
      val con = addCon(primitiveAtom)
      addClass(Loc.builtin, con, List(a), List(primitive(VarT(a))), List(_))
    }

    for ((t, d) <- primTypes) {
      addInstance(primitiveAtom, primInstance(primitiveAtom, t, d))
    }

    primOp(
      Global("Builtin", "withNull"),
      Fun("Builtin.withNull", {
        case Prim(t : PrimT) => Prim(t.withNull)
      }),
      FA(a => primitiveAtom(a) =>: prim(a) ->: prim(nullable(a)))
    )

    // class Unscaled a
    val unscaled = {
      val a = freshType(star)
      addClass(Loc.builtin, addCon(mkClassCon(Global("Builtin","Unscaled"))),
               List(a), List(), List(_))
    }
    for (b <- primBindings) {
      val (_, d, AppT(_, t), scaledp) = b
      val cla = if (scaledp) scaled else unscaled
      addInstance(cla, primInstance(cla, t, d))
      addInstance(cla, primInstance(cla, nullable(t), d.withNull))
    }

    // class Num a | PrimitiveNum a
    val num = {
      val a = freshType(star)
      val con = addCon(mkClassCon(Global("Builtin","Num")))
      addClass(Loc.builtin, con, List(a), List(primitiveNum(VarT(a))), _ => List())
    }

    for ((t,d) <- primNumTypes) {
      addInstance(num, primInstance(num,t,d))
    }
  }

  // primitive IO support
  def interop(implicit s: SessionEnv, su: Supply) {
    addCon(io)
    val throwable = addCon(mkCon[Throwable](Global("Native.Throwable","Throwable")))
    primOp(Global("IO.Unsafe","eval"), fun3((t,c,e) => try {
      val r = e.extract[FFI[_]].eval
      t(Prim(r))
    } catch {
      case err: Throwable => c(Prim(err))
    }), FA(a => FA(r => (a ->: r) ->: (throwable ->: r) ->: ffi(a) ->: r)))
    primOp(Global("Native.Throwable","raise"), Fun("Native.Throwable.raise", { case Prim(e : Throwable) => Bottom(throw e) }), FA(a => throwable ->: a))
    primOp(Global("Builtin", "IO"), Fun(f => Data(Global("Builtin","IO"),Array(f))),
      FA(a =>
        FA(r => {
          val t = FA(i => (i ->: r) ->: (throwable ->: r) ->: ffi(i) ->: r)
          ((a ->: r) ->: t ->: (throwable ->: r) ->: r)
        }) ->: io(a)
      )
    )

    val function0 = addCon(mkCon[Function0[_]](Global("Native.Function","Function0"), star ->: star))
    primOp(Global("Native.Function","force"), Fun(v => Prim(v.extract[Function0[_]].apply())), FA(a => function0(a) ->: a))
    primOp(Global("Native.Function","delay"), Fun(v => Prim(() => v.extract[Any])), FA(a => a ->: function0(a)))
    val function1 = addCon(mkCon[Function1[_,_]](Global("Native.Function","Function1"), star ->: star ->: star))
    primOp(Global("Native.Function","function1"),  Fun("Native.Function.function1", { case Fun(f) => Prim((x: Any) => f(Prim(x)).extract[Any]) }),
                         FA(a => FA(b => (a ->: b) ->: function1(a, b))))
    val function2 = addCon(mkCon[Function2[_,_,_]](Global("Native.Function","Function2"), star ->: star ->: star ->: star))
    primOp(Global("Native.Function","function2"), Fun(fn => Prim((x: Any, y: Any) => fn(Prim(x)).apply(Prim(y)).extract[Any])),
        FA(a => FA(b => FA(c => (a ->: b ->: c) ->: function2(a, b, c)))))
    val function3 = addCon(mkCon[Function3[_,_,_,_]](Global("Native.Function","Function3"), star ->: star ->: star ->: star ->: star))
    primOp(Global("Native.Function","function3"), Fun(fn => Prim((x: Any, y: Any, z: Any) => fn(Prim(x)).apply(Prim(y)).apply(Prim(z)).extract[Any])),
        FA(a => FA(b => FA(c => FA(d => (a ->: b ->: c ->: d) ->: function3(a, b, c, d))))))
    primOp(Global("Error","error"), Fun(s => Bottom(error(s.extract[String]))), FA(a => string ->: a))
    primOp(Global("Unsafe.Coerce","unsafeCoerce"), Fun(x => x), FA(a => FA(b => a ->: b)))
    addCon(primExpr)
    primOp(Global("Prim","primExpr##"),
               Fun(x => Prim(toPrimExpr(x))),
               FA(a => a ->: primExpr))
    primOp(Global("Prim","unsafePrimExprIn##"),
               Fun(_.whnfMatch("Prim.primExpr##"){
                 case Prim(x: PrimExpr) => Prim(fromPrimExpr(x))}),
               FA(a => primExpr ->: a))
  }

  def refl(implicit s: SessionEnv, su: Supply) {
    val eq = freshKind match { case a =>
      addCon(mkConEx[AnyRef](Global("Type.Eq","==",InfixN(4)),KindSchema(builtin, List(a), VarK(a) ->: VarK(a) ->: star)))
    }
    primOp(Global("Type.Eq","Refl"), Data(Global("Type.Eq","Refl")), {
      val k = freshKind
      val a = freshType(VarK(k))
      Forall(builtin, List(k), List(a), Exists(builtin), eq(VarT(a),VarT(a)))
    })
    primOp(
      Global("Type.Eq","subst"),
      Fun("Type.Eq.subst", { case Data(Global("Type.Eq","Refl",Idfix), _) => Fun(a => a) }), {
      val k = freshKind
      val a = freshType(VarK(k))
      val b = freshType(VarK(k))
      val p = freshType(VarK(k) ->: star)
      Forall(builtin, List(k), List(a,b,p), Exists(builtin), eq(VarT(a),VarT(b)) ->: VarT(p)(VarT(a)) ->: VarT(p)(VarT(b)))
    })
  }

  def preamble(implicit s: SessionEnv, su: Supply) {
    cons; simple; relations; prims; interop; refl
  }
}
