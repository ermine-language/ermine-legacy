package com.clarifi.reporting

import java.util.Calendar
import java.util.Date

import scalaz._
import scalaz.Scalaz._
import Equal._
import Show._

import com.clarifi.reporting.ReportingUtils.splitWith

/** An expression to be evaluated in the environment of a record. */
sealed abstract class Op extends TraversableColumns[Op] {
  import Op._

  /** Fold. */
  def apply[z](opliteral: (PrimExpr) => z,
               columnvalue: (ColumnName, PrimT) => z,
               add: (z, z) => z,
               sub: (z, z) => z,
               mul: (z, z) => z,
               floordiv: (z, z) => z,
               doublediv: (z, z) => z,
               pow: (z, z) => z,
               concat: (List[z]) => z,
               oif: (Predicate, => z, => z) => z, // lazy makes sense for If
               coalesce: (z, => z) => z,
               dateadd: (z, Int, TimeUnit) => z,
               funcall: (String, String, List[String], List[z], PrimT) => z): z = {
    def rec(o: Op): z = o match {
      case OpLiteral(lit) => opliteral(lit)
      case ColumnValue(col, pt) => columnvalue(col, pt)
      case Add(l, r) => add(rec(l), rec(r))
      case Sub(l, r) => sub(rec(l), rec(r))
      case Mul(l, r) => mul(rec(l), rec(r))
      case FloorDiv(l, r) => floordiv(rec(l), rec(r))
      case DoubleDiv(l, r) => doublediv(rec(l), rec(r))
      case Pow(l, r) => pow(rec(l), rec(r))
      case Concat(cs) => concat(cs map rec)
      case If(t, c, a) => oif(t, rec(c), rec(a))
      case Coalesce(l, r) => coalesce(rec(l), rec(r))
      case DateAdd(o, n, u) => dateadd(rec(o), n, u)
      case Funcall(n, d, spc, args, ty) => funcall(n, d, spc, args map rec, ty)
    }
    rec(this)
  }

  /** Evaluate this op in the environment `t`.  Throws if a column is
    * missing or there is a type mismatch.
    */
  def eval(t: Record): PrimExpr = apply[PrimExpr](
    opliteral = (lit) => lit,
    columnvalue = (n, _) => t.getOrElse(n, sys.error("missing column: " + n + " in " + t.keySet)),
    add = (_ + _),
    sub = (_ - _),
    mul = (_ * _),
    floordiv = (_ / _),
    doublediv = (_ / _),
    pow = (_ pow _),
    concat = xs => StringExpr(false, xs.map(_.extractString).concatenate),
    oif = (test, c, a) => if (test eval t) c else a,
    coalesce = (l, r) => l match { case NullExpr(_) => r ; case _ => l },
    dateadd = (d, n, u) => d match {
      case NullExpr(_) => d
      case _ => DateExpr(false, u.increment(d.extractDate, n))
    },
    funcall = (n, _, _, _, _) =>
                 sys error ("Can't invoke %s outside a database" format n))

  def simplify(t: Map[ColumnName, Op]): Op = {
    def pnum(id: Byte)(p: PrimExpr) = p match {
      case ByteExpr(_, d) => d === id
      case ShortExpr(_, d) => d === id
      case IntExpr(_, i) => i === id
      case LongExpr(_, d) => d === id
      case DoubleExpr(_, d) => d === id
      case _: StringExpr | _: DateExpr | _: BooleanExpr | _: UuidExpr
         | _: NullExpr => false
    }
    def opbin(unsimpl: (Op, Op) => Op, simpl: (PrimExpr, PrimExpr) => PrimExpr,
              lident: PrimExpr => Boolean, rident: PrimExpr => Boolean
            )(l: Op, r: Op) = (l, r) match {
      case (OpLiteral(l), OpLiteral(r)) => OpLiteral(simpl(l, r))
      case (OpLiteral(l), r) if lident(l) => r
      case (l, OpLiteral(r)) if rident(r) => l
      case (l, r) => unsimpl(l, r)
    }
    apply[Op](opliteral = OpLiteral,
              columnvalue = (n, ty) =>
                t get n map (_ simplify t) getOrElse ColumnValue(n, ty),
              add = opbin(Add, (_ + _), pnum(0), pnum(0)),
              sub = opbin(Sub, (_ - _), Function const false, pnum(0)),
              mul = opbin(Mul, (_ * _), pnum(1), pnum(1)),
              floordiv = opbin(FloorDiv, (_ / _),
                               Function const false, pnum(1)),
              doublediv = opbin(DoubleDiv, (_ / _),
                                Function const false, pnum(1)),
              pow = opbin(Pow, (_ pow _), Function const false, pnum(1)),
              concat = {xs =>
                splitWith(xs map {case OpLiteral(lit) => Left(lit)
                                  case op => Right(op)})(_.isLeft).toList flatMap {
                  case lits@(Left(_) :: _) =>
                    List(OpLiteral(StringExpr(
                      false, lits.map(_.left.get.extractString).suml)))
                  case unsimpl => unsimpl flatMap (_.right.toSeq)
                } filter {case OpLiteral(StringExpr(_, "")) => false
                          case _ => true} match {
                  case List() => OpLiteral(StringExpr(false, ""))
                  case List(lit@OpLiteral(_)) => lit
                  case unsimpl => Concat(unsimpl)
                }},
              oif = ((test, c, a) =>
                Predicates simplify (test liftOp (_ simplify t: Id[Op])) match {
                  case Predicate.Atom(b) => if (b) c else a
                  case pr => If(pr, c, a)
              }),
              coalesce = (l, r) => Coalesce(l, r),
              dateadd = (d, n, u) => DateAdd(d, n, u),
              funcall = Funcall)
  }

  def guessTypeUnsafe: PrimT =
    guessType.fold(s => sys.error(s.head), t => t)

  /** Try to type me.  Failure doesn't necessarily mean I won't run
    * in a `Project`. */
  def guessType: ValidationNel[String, PrimT] = {
    import PrimT._
    type M[A] = ValidationNel[String, A]
    def numRank(t: PrimT): Option[Int] = t match {
      case ByteT(_) => Some(10)
      case ShortT(_) => Some(20)
      case IntT(_) => Some(30)
      case LongT(_) => Some(40)
      case DoubleT(_) => Some(50)
      case _ => None
    }
    // Autopromoting numeric type unification.
    def numbin(mleft: M[PrimT], mright: M[PrimT]): M[PrimT] =
      (mleft |@| mright)(_ -> _) flatMap {case (left, right) =>
        (numRank(left), numRank(right), left sup right) match {
          case (None, _, _) => ("Nonnumeric type " + left).failureNel
          case (_, None, _) => ("Nonnumeric type " + right).failureNel
          case (_, _, Some(t)) => t.success
          case (Some(rkl), Some(rkr), _) =>
            (if (rkl < rkr) right else left).success
      }}
    apply[M[PrimT]](
      opliteral = x => x.typ |> (_.success),
      columnvalue = (_, typ) => typ.success,
      add = numbin,
      sub = numbin,
      mul = numbin,
      floordiv = numbin,
      doublediv = numbin,
      pow = numbin,
      concat = xs => xs.sequence map (Function const StringT(0, false)),
      oif = (_, mc, ma) => (mc |@| ma)(_ -> _) flatMap {case (c, a) =>
        c sup a map (_.success) getOrElse
        ("Unmatched if branches %s and %s" format (c, a) failureNel)},
      coalesce = (_, t) => t,
      dateadd = (d, _, _) => d, // type of date arithmetic is always a date
      funcall = (name, db, ns, args, ty) => args.sequence >| ty)
  }

  /** Post-order replace the expression tree, with traversal. */
  def postReplace[F[_]: Monad](f: Op => F[Op]): F[Op] = {
    def binop(b: (Op, Op) => Op) =
      (fl: F[Op], fr: F[Op]) => b.lift[F].apply(fl, fr) >>= f
    apply[F[Op]](
      opliteral = f compose OpLiteral,
      columnvalue = (n, t) => f(ColumnValue(n, t)),
      add = binop(Add),
      sub = binop(Sub),
      mul = binop(Mul),
      floordiv = binop(FloorDiv),
      doublediv = binop(DoubleDiv),
      pow = binop(Pow),
      concat = _.sequence flatMap (f compose Concat),
      oif = (t, c, a) => ((t postReplaceOp f) |@| c |@| a)(If) >>= f,
      coalesce = (l, r) => (l |@| r)(Coalesce),
      dateadd = (d, n, u) => d.map(DateAdd(_,n,u)),
      funcall = (name, db, ns, args, ty) => args.sequence flatMap (args =>
                  f(Funcall(name, db, ns, args, ty))))
  }

  /** Traverse the column references in an `Op`. */
  def traverseColumns[F[_]: Applicative](f: ColumnName => F[ColumnName]): F[Op] = {
    def binop[A](liftee: (A, A) => A) = liftee.lift[F]
    apply[F[Op]](
      opliteral = (lit) => (OpLiteral(lit): Op).pure[F],
      columnvalue = (c, ty) => f(c) map (ColumnValue(_, ty)),
      add = binop(Add(_, _)),
      sub = binop(Sub(_, _)),
      mul = binop(Mul(_, _)),
      floordiv = binop(FloorDiv(_, _)),
      doublediv = binop(DoubleDiv(_, _)),
      pow = binop(Pow(_, _)),
      concat = {cl => cl.sequence map (Concat(_))},
      oif = (test, c, a) => ((test traverseColumns f) |@| c |@| a)(If),
      coalesce = (l, r) => (l |@| r)(Coalesce),
      dateadd = (d, n, u) => d.map(DateAdd(_,n,u)),
      funcall = ((name, db, ns, args, ty) =>
                 args.sequence map (Funcall(name, db, ns, _, ty))))
  }

  def typedColumnFoldMap[Z: Monoid](f: (ColumnName, PrimT) => Z): Z = {
    type WM[A] = Writer[Z, A]
    postReplace[WM]{
      case it@Op.ColumnValue(n, t) => (it:Op) set f(n, t)
      case it => it.point[WM]
    }.written
  }
}

trait TimeUnit {
  import TimeUnit._ // constructors

  /**
   * Increment `d` by `n` units. Example: `Day.increment(1/1/2013, 10)`
   * yields `1/11/2013`.
   */
  def increment(d: Date, n: Int): Date = {
    def go(d: Date, untypedJavaCalendarUnits: Int, n: Int): Date = {
      val cal = Calendar.getInstance
      cal.setTime(d)
      cal.add(untypedJavaCalendarUnits, n)
      cal.getTime
    }
    val (units, n2) = this match {
      case Day => (Calendar.DATE, n)
      case Week => (Calendar.DATE, n*7)
      case Month => (Calendar.MONTH, n)
      case Year => (Calendar.YEAR, n)
    }
    go(d, units, n2)
  }
}

object TimeUnit {
  // case object Second extends TimeUnit
  case object Day extends TimeUnit
  case object Week extends TimeUnit
  case object Month extends TimeUnit
  // case object Quarter extends TimeUnit
  case object Year extends TimeUnit
}

object TimeUnits {
  val Day = TimeUnit.Day
  val Week = TimeUnit.Week
  val Month = TimeUnit.Month
  // val Quarter = TimeUnit.Quarter
  val Year = TimeUnit.Year
}

// for easier foreign importing by Ermine
object Ops {
  def dateAdd(n: Int, units: TimeUnit, date: Op): Op =
    Op.DateAdd(date, n, units)
  def coalesce(l: Op, r: Op): Op = Op.Coalesce(l, r)
}

object Op {
  case class OpLiteral(lit: PrimExpr) extends Op
  case class ColumnValue(col: ColumnName, typ: PrimT) extends Op
  case class Add(l: Op, r: Op) extends Op
  case class Sub(l: Op, r: Op) extends Op
  case class Mul(l: Op, r: Op) extends Op
  case class FloorDiv(l: Op, r: Op) extends Op
  case class DoubleDiv(l: Op, r: Op) extends Op
  case class Pow(l: Op, r: Op) extends Op
  case class Concat(cs: List[Op]) extends Op
  case class If(test: Predicate, consequent: Op, alternate: Op) extends Op
  case class Coalesce(l: Op, r: Op) extends Op
  case class DateAdd(date: Op, n: Int, units: TimeUnit) extends Op
  case class Funcall(name: String, database: String, namespace: List[String],
                     args: List[Op], typ: PrimT) extends Op

  implicit val OpEqual: Equal[Op] = equalA
  implicit val OpShow: Show[Op] = showFromToString
}

