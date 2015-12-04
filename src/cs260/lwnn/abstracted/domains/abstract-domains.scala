package cs260.lwnn.abstracted.domains

import cs260.lwnn.syntax._
import cs260.lwnn.util._

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// ClassDefs
//
// the class definitions are invariant, so we can factor them out into
// one global version rather than having one per state as in the
// formal semantics

case object θ {
  type FieldMap = Map[Var, Type]
  type MethodMap = Map[MethodName, Method]

  // ... (same as for the concrete semantics)
  var classdefs = Map[ClassName, (FieldMap, MethodMap)]("TopClass" -> (Map(), Map()))

  def apply(cn: ClassName): (FieldMap, MethodMap) = {
    classdefs(cn)
  }
  def getFields(cn: ClassName): FieldMap = {
    classdefs(cn)._1
  }
  def getMethods(cn: ClassName): MethodMap = {
    classdefs(cn)._2
  }
  def getMethod(cn: ClassName, mn: ClassName): Method = {
    classdefs(cn)._2(mn)
  }

  def +(newclassdef: (ClassName, (FieldMap, MethodMap))) =
    {
      assert(!(classdefs contains newclassdef._1))
      classdefs += newclassdef
    }
}

//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals(x2v: Map[Var, Value]) {
  // ...
  def apply(x: Var): Value =
    x2v(x)

  def +(xv: (Var, Value)): Locals = {
    Locals(x2v + xv)
  }
  def widening(l: Locals): Locals = {
    Locals(this.x2v ++ l.x2v.map { case (x, v) => x -> (this.x2v.getOrElse(x, v) ⊔ v) })
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Heap
//
// NOTE: in this version, we always weakly update the heap. for
// convenience, a Heap maintains two maps, one for objects and one for
// continuation stacks. In other words, there will be a map for
// Address to Object and also a Map for Address to sets of
// continuation stacks. Thus, there will be two different methods for
// accessing the heap (one for accessing objects, one for accessing
// continuation stacks) and two different methods for updating the
// heap (ditto).

case class Heap(a2o: Map[Address, Object], a2k: Map[Address, Set[Seq[Kont]]]) {
  // ...
  def applyO(a: Address): Object = {
    a2o(a)
  }
  def applyK(ak: Address): Set[Seq[Kont]] = {
    a2k(ak)
  }
  def addO(ao: (Address, Object)): Heap = {
    if (a2o contains ao._1) {
      val o = a2o(ao._1) ⊔ ao._2
      val new_ao = (ao._1, o)
      Heap(a2o + new_ao, a2k)
    } else
      Heap(a2o + ao, a2k)
  }
  def addK(ak: (Address, Seq[Kont])): Heap = {
    if (a2k contains ak._1) Heap(a2o, a2k + (ak._1 -> (a2k(ak._1) + ak._2)))
    else Heap(a2o, a2k + (ak._1 -> Set(ak._2)))
  }
  def widening(h: Heap): Heap = {
    val newa2o = a2o ++ h.a2o.map { case (a, o) => a -> (a2o.getOrElse(a, o) ⊔ o) }
    val newa2k = a2k ++ h.a2k.map { case (a, k) => a -> (a2k.getOrElse(a, k) ++ k) }
    Heap(newa2o, newa2k);
  }
}

sealed abstract class Value {
  def is_⊥ : Boolean
  def ⊔(v: Value): Value
  def +(v: Value): Value
  def −(v: Value): Value
  def ×(v: Value): Value
  def ÷(v: Value): Value
  def <(v: Value): Value
  def ≤(v: Value): Value
  def ∧(v: Value): Value
  def ∨(v: Value): Value
  def ≈(v: Value): Value
  def ≠(v: Value): Value
}

sealed abstract class ℤ extends Value {
  override def is_⊥ : Boolean = this match {
    case ZBOT ⇒ true
    case _    ⇒ false
  }
  override def ⊔(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ v
      case (_, ZBOT)      ⇒ this
      case (ZPOS, ZPOS)   ⇒ ZPOS
      case (ZNEG, ZNEG)   ⇒ ZNEG
      case (ZZERO, ZZERO) ⇒ ZZERO
      case (_, _)         ⇒ ZTOP
    }
    case _ ⇒ ZBOT
  }
  override def +(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ ZBOT
      case (_, ZBOT)      ⇒ ZBOT
      case (ZPOS, ZPOS)   ⇒ ZPOS
      case (ZPOS, ZZERO)  ⇒ ZPOS
      case (ZNEG, ZNEG)   ⇒ ZNEG
      case (ZNEG, ZZERO)  ⇒ ZNEG
      case (ZZERO, ZZERO) ⇒ ZZERO
      case (ZZERO, ZNEG)  ⇒ ZNEG
      case (ZZERO, ZPOS)  ⇒ ZPOS
      case (_, _)         ⇒ ZTOP
    }
    case _ ⇒ ZBOT
  }
  override def −(v: Value): Value = v match {
    case z: ℤ ⇒ (this, z) match {
      case (ZBOT, _)      ⇒ ZBOT
      case (_, ZBOT)      ⇒ ZBOT
      case (ZPOS, ZZERO)  ⇒ ZPOS
      case (ZPOS, ZNEG)   ⇒ ZPOS
      case (ZNEG, ZZERO)  ⇒ ZNEG
      case (ZNEG, ZPOS)   ⇒ ZNEG
      case (ZZERO, ZZERO) ⇒ ZZERO
      case (ZZERO, ZNEG)  ⇒ ZPOS
      case (ZZERO, ZPOS)  ⇒ ZNEG
      case (_, _)         ⇒ ZTOP
    }
    case _ ⇒ ZBOT
  }
  override def ×(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ ZBOT
      case (_, ZBOT)      ⇒ ZBOT
      case (ZPOS, ZPOS)   ⇒ ZPOS
      case (ZPOS, ZNEG)   ⇒ ZNEG
      case (ZPOS, ZZERO)  ⇒ ZZERO
      case (ZNEG, ZPOS)   ⇒ ZNEG
      case (ZNEG, ZNEG)   ⇒ ZPOS
      case (ZNEG, ZZERO)  ⇒ ZZERO
      case (ZZERO, ZPOS)  ⇒ ZZERO
      case (ZZERO, ZNEG)  ⇒ ZZERO
      case (ZZERO, ZZERO) ⇒ ZZERO
      case (ZZERO, ZTOP)  ⇒ ZZERO
      case (_, _)         ⇒ ZTOP
    }
    case _ ⇒ ZBOT
  }
  override def ÷(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)    ⇒ ZBOT
      case (_, ZBOT)    ⇒ ZBOT
      case (ZPOS, ZPOS) ⇒ ZPOS
      case (ZPOS, ZNEG) ⇒ ZNEG
      case (ZPOS, ZZERO) ⇒ {
        ZBOT
      }
      case (ZNEG, ZPOS) ⇒ ZNEG
      case (ZNEG, ZNEG) ⇒ ZPOS
      case (ZNEG, ZZERO) ⇒ {
        ZBOT
      }
      case (ZZERO, ZPOS) ⇒ ZZERO
      case (ZZERO, ZNEG) ⇒ ZZERO
      case (ZZERO, ZTOP) ⇒ ZZERO
      case (ZZERO, ZZERO) ⇒ {
        ZBOT
      }
      case (ZTOP, ZZERO) ⇒ ZBOT
      case (_, _)        ⇒ ZTOP
    }
    case _ ⇒ ZBOT
  }
  override def <(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ Bool.⊥
      case (_, ZBOT)      ⇒ Bool.⊥
      case (ZPOS, ZNEG)   ⇒ Bool.False
      case (ZPOS, ZZERO)  ⇒ Bool.False
      case (ZNEG, ZPOS)   ⇒ Bool.True
      case (ZNEG, ZZERO)  ⇒ Bool.True
      case (ZZERO, ZPOS)  ⇒ Bool.True
      case (ZZERO, ZZERO) ⇒ Bool.False
      case (ZZERO, ZNEG)  ⇒ Bool.False
      case (_, _)         ⇒ Bool.⊤
    }
    case _: Bool | _: Str | _: Reference ⇒ Bool.⊥
  }
  override def ≤(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ Bool.⊥
      case (_, ZBOT)      ⇒ Bool.⊥
      case (ZPOS, ZNEG)   ⇒ Bool.False
      case (ZPOS, ZZERO)  ⇒ Bool.False
      case (ZNEG, ZPOS)   ⇒ Bool.True
      case (ZNEG, ZZERO)  ⇒ Bool.True
      case (ZZERO, ZPOS)  ⇒ Bool.True
      case (ZZERO, ZZERO) ⇒ Bool.True
      case (ZZERO, ZNEG)  ⇒ Bool.False
      case (_, _)         ⇒ Bool.⊤
    }
    case _: Bool | _: Str | _: Reference ⇒ Bool.⊥
  }
  override def ≈(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ Bool.⊥
      case (_, ZBOT)      ⇒ Bool.⊥
      case (ZPOS, ZNEG)   ⇒ Bool.False
      case (ZPOS, ZZERO)  ⇒ Bool.False
      case (ZNEG, ZPOS)   ⇒ Bool.False
      case (ZNEG, ZZERO)  ⇒ Bool.False
      case (ZZERO, ZPOS)  ⇒ Bool.False
      case (ZZERO, ZZERO) ⇒ Bool.True
      case (ZZERO, ZNEG)  ⇒ Bool.False
      case (_, _)         ⇒ Bool.⊤
    }
    case Bool.⊥ | Str.⊥ | Reference.⊥    ⇒ Bool.⊥
    case _: Bool | _: Str | _: Reference ⇒ Bool.False
  }
  override def ≠(v: Value): Value = v match {
    case _: ℤ ⇒ (this, v) match {
      case (ZBOT, _)      ⇒ Bool.⊥
      case (_, ZBOT)      ⇒ Bool.⊥
      case (ZPOS, ZNEG)   ⇒ Bool.True
      case (ZPOS, ZZERO)  ⇒ Bool.True
      case (ZNEG, ZPOS)   ⇒ Bool.True
      case (ZNEG, ZZERO)  ⇒ Bool.True
      case (ZZERO, ZPOS)  ⇒ Bool.True
      case (ZZERO, ZZERO) ⇒ Bool.False
      case (ZZERO, ZNEG)  ⇒ Bool.True
      case (_, _)         ⇒ Bool.⊤
    }
    case Bool.⊥ | Str.⊥ | Reference.⊥    ⇒ Bool.⊥
    case _: Bool | _: Str | _: Reference ⇒ Bool.True
  }
  override def ∧(v: Value): Value = {
    Bool.⊥
  }
  override def ∨(v: Value): Value = {
    Bool.⊥
  }
}

case object ZPOS extends ℤ
case object ZNEG extends ℤ
case object ZZERO extends ℤ
case object ZTOP extends ℤ
case object ZBOT extends ℤ

object ℤ {
  val ⊤ = ZTOP
  val ⊥ = ZBOT
  def α(ns: Set[BigInt]): ℤ =
    {
      var zero = false
      var neg = false
      var pos = false
      ns foreach (n ⇒
        if (n == 0) zero |= true
        else if (n > 0) pos |= true
        else neg |= true)

      (neg, zero, pos) match {
        case (false, false, false) ⇒ ZBOT
        case (true, false, false)  ⇒ ZNEG
        case (false, true, false)  ⇒ ZZERO
        case (false, false, true)  ⇒ ZPOS
        case (_, _, _)             ⇒ ZTOP
      }
    }

  def α(n: BigInt): ℤ =
    α(Set(n))
}

case class Bool(bs: Set[Boolean]) extends Value {
  // ...
  override def is_⊥ : Boolean = { if (bs.isEmpty) true else false }
  override def ⊔(v: Value): Value = v match {
    case b: Bool ⇒ (this, b) match {
      case (_, Bool.⊥)              ⇒ this
      case (Bool.⊥, _)              ⇒ b
      case (Bool.True, Bool.False)  ⇒ Bool.⊤
      case (Bool.True, Bool.True)   ⇒ Bool.True
      case (Bool.False, Bool.True)  ⇒ Bool.⊤
      case (Bool.False, Bool.False) ⇒ Bool.False
      case (Bool.⊤, _)              ⇒ Bool.⊤
      case (_, Bool.⊤)              ⇒ Bool.⊤
    }
    case _ ⇒ Bool.⊥
  }

  override def +(v: Value): Value = {
    Bool.⊥
  }
  override def −(v: Value): Value = {
    Bool.⊥
  }
  override def ×(v: Value): Value = {
    Bool.⊥
  }
  override def ÷(v: Value): Value = {
    Bool.⊥
  }
  override def <(v: Value): Value = {
    Bool.⊥
  }
  override def ≤(v: Value): Value = {
    Bool.⊥
  }
  override def ∧(v: Value): Value = v match {
    case b: Bool ⇒ (this, b) match {
      case (Bool.⊥, _)            ⇒ Bool.⊥
      case (_, Bool.⊥)            ⇒ Bool.⊥
      case (Bool.True, Bool.True) ⇒ Bool.True
      case (_, Bool.False)        ⇒ Bool.False
      case (Bool.False, _)        ⇒ Bool.False
      case (_, _)                 ⇒ Bool.⊤
    }
    case _ ⇒ Bool.⊥
  }
  override def ∨(v: Value): Value = v match {
    case b: Bool ⇒ (this, b) match {
      case (Bool.⊥, _)              ⇒ b
      case (_, Bool.⊥)              ⇒ this
      case (Bool.False, Bool.False) ⇒ Bool.False
      case (_, Bool.True)           ⇒ Bool.True
      case (Bool.True, _)           ⇒ Bool.True
      case (_, _)                   ⇒ Bool.⊤
    }
    case _ ⇒ Bool.⊥
  }
  override def ≈(v: Value): Value = v match {
    case b: Bool ⇒ (this, b) match {
      case (Bool.⊥, _)              ⇒ Bool.⊥
      case (_, Bool.⊥)              ⇒ Bool.⊥
      case (Bool.True, Bool.True)   ⇒ Bool.True
      case (Bool.True, Bool.False)  ⇒ Bool.False
      case (Bool.False, Bool.False) ⇒ Bool.True
      case (Bool.False, Bool.True)  ⇒ Bool.False
      case (_, _)                   ⇒ Bool.⊤
    }
    case ZBOT | Str.⊥ | Reference.⊥ => Bool.⊥
    case _                          => Bool.False
  }
  override def ≠(v: Value): Value = v match {
    case b: Bool ⇒ (this, b) match {
      case (Bool.⊥, _)              ⇒ Bool.⊥
      case (_, Bool.⊥)              ⇒ Bool.⊥
      case (Bool.True, Bool.True)   ⇒ Bool.False
      case (Bool.True, Bool.False)  ⇒ Bool.True
      case (Bool.False, Bool.False) ⇒ Bool.False
      case (Bool.False, Bool.True)  ⇒ Bool.True
      case (_, _)                   ⇒ Bool.⊤
    }
    case ZBOT | Str.⊥ | Reference.⊥ => Bool.⊥
    case _                          => Bool.True
  }

  override def toString =
    if (bs.size == 1) bs.head.toString
    else "{true, false}"
}

object Bool {
  val ⊤ = Bool(Set(true, false))
  val ⊥ = Bool(Set())
  val True = Bool(Set(true))
  val False = Bool(Set(false))

  def α(bs: Set[Boolean]): Bool =
    Bool(bs)
  def α(b: Boolean): Bool =
    α(Set[Boolean](b))
}
sealed abstract class Str extends Value {
  override def is_⊥ : Boolean =
    if (this == SBOT) true else false
  override def ⊔(v: Value): Value = v match {
    case _: Str ⇒ (this, v) match {
      case (SBOT, SBOT) ⇒ SBOT
      case (_, _)       ⇒ STOP
    }
    case _ ⇒ SBOT
  }
  override def <(v: Value): Value = v match {
    case s: Str ⇒ (this, s) match {
      case (SBOT, _)    ⇒ Bool.⊥
      case (_, SBOT)    ⇒ Bool.⊥
      case (STOP, STOP) ⇒ Bool.⊤
    }
    case _ ⇒ SBOT
  }
  override def ≤(v: Value): Value = v match {
    case s: Str ⇒ (this, s) match {
      case (SBOT, _)    ⇒ Bool.⊥
      case (_, SBOT)    ⇒ Bool.⊥
      case (STOP, STOP) ⇒ Bool.⊤
    }
    case _ ⇒ SBOT
  }
  override def +(v: Value): Value = v match {
    case s: Str ⇒ (this, s) match {
      case (SBOT, _) ⇒ SBOT
      case (_, SBOT) ⇒ SBOT
      case (_, _)    ⇒ STOP
    }
    case _ ⇒ SBOT
  }
  override def ≈(v: Value): Value = v match {
    case s: Str ⇒ (this, s) match {
      case (SBOT, _)    ⇒ Bool.⊥
      case (_, SBOT)    ⇒ Bool.⊥
      case (STOP, STOP) ⇒ Bool.⊤
    }
    case ZBOT | Bool.⊥ | Reference.⊥   ⇒ Bool.⊥
    case _: ℤ | _: Bool | _: Reference => Bool.False
  }
  override def ≠(v: Value): Value = v match {
    case s: Str ⇒ (this, s) match {
      case (SBOT, _)    ⇒ Bool.⊥
      case (_, SBOT)    ⇒ Bool.⊥
      case (STOP, STOP) ⇒ Bool.⊤
    }
    case ZBOT | Bool.⊥ | Reference.⊥   ⇒ Bool.⊥
    case _: ℤ | _: Bool | _: Reference => Bool.True
  }
  override def −(v: Value): Value = {
    SBOT
  }
  override def ×(v: Value): Value = {
    SBOT
  }
  override def ÷(v: Value): Value = {
    SBOT
  }
  override def ∧(v: Value): Value = {
    Bool.⊥
  }
  override def ∨(v: Value): Value = {
    Bool.⊥
  }
}

case object STOP extends Str
case object SBOT extends Str

object Str {
  val ⊤ = STOP // ...
  val ⊥ = SBOT // ...

  def α(strs: Set[String]): Str =
    // ...
    { if (strs.isEmpty) ⊥ else ⊤ }
}

// for convenience we'll keep a set of addresses and separately a
// boolean indicating whether the reference could also be Null.
case class Reference(as: Set[Address], nil: Boolean = false) extends Value {
  // ...

  override def is_⊥ : Boolean =
    if (as.isEmpty && nil == false) true else false

  override def ⊔(v: Value): Value = v match {
    case ref: Reference ⇒ (this, ref) match {
      case (Reference.⊥, _)    ⇒ ref
      case (_, Reference.⊥)    ⇒ this
      case (Reference.Null, _) ⇒ Reference(ref.as, true)
      case (_, Reference.Null) ⇒ Reference(as, true)
      case (_, _)              ⇒ Reference(as ++ ref.as, nil || ref.nil)

    }
    case _ ⇒ Reference.⊥
  }
  override def ≈(v: Value): Value = v match {
    case ref: Reference ⇒ (this, ref) match {
      case (Reference.⊥, _) ⇒ Bool.⊥
      case (_, Reference.⊥) ⇒ Bool.⊥
      case (_, _) ⇒ if (!(nil && ref.nil) && (as & ref.as).isEmpty) Bool.False
      else Bool.⊤
    }
    case ZBOT | Bool.⊥ | SBOT => Bool.⊥
    case _                    ⇒ Bool.False
  }
  override def ≠(v: Value): Value = v match {
    case ref: Reference ⇒ (this, ref) match {
      case (Reference.⊥, _) ⇒ Bool.⊥
      case (_, Reference.⊥) ⇒ Bool.⊥
      case (_, _) ⇒ if (!(nil && ref.nil) && (as & ref.as).isEmpty) Bool.True
      else Bool.⊤
    }
    case ZBOT | Bool.⊥ | SBOT => Bool.⊥
    case _                    ⇒ Bool.True
  }
  override def +(v: Value): Value = {
    ZBOT
  }
  override def −(v: Value): Value = {
    ZBOT
  }
  override def ×(v: Value): Value = {
    ZBOT
  }
  override def ÷(v: Value): Value = {
    ZBOT
  }
  override def <(v: Value): Value = {
    ZBOT
  }
  override def ≤(v: Value): Value = {
    ZBOT
  }
  override def ∧(v: Value): Value = {
    ZBOT
  }
  override def ∨(v: Value): Value = {
    ZBOT
  }

  override def toString =
    if (as.isEmpty && nil) "null"
    else if (as.size == 1 && !nil) as.head.toString
    else {
      val addrs = as map (_.toString)
      val strs = if (nil) addrs + "null" else addrs
      "{" + strs.mkString(",") + "}"
    }
}

object Reference {
  val ⊥ = Reference(Set(), false) // ...
  val Null = Reference(Set(), true) // ...

  def apply(a: Address): Reference = {
    // ...
    Reference(Set(a), false)
  }
}

// abstract addresses will be the AST node id of the left-hand side
// variable of the New statement that allocates the address.
case class Address(loc: Int) {
  override def toString =
    "addr" + loc
}

//——————————————————————————————————————————————————————————————————————————————
// Object

case class Object(cn: ClassName, flds: Map[Var, Value]) {
  def ⊔(o: Object): Object = {
    // ...
    assert(cn == o.cn)
    Object(cn, flds.map {
      case (x, v) ⇒ if (o.flds contains x) (x, v ⊔ o.flds(x))
      else (x, v)
    })
  }

  def apply(x: Var): Value =
    flds(x)

  def +(xv: (Var, Value)): Object = {
    Object(cn, flds + xv)
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
case class StmtK(s: Stmt) extends Kont
case class WhileK(e: Exp, ss: Seq[Stmt]) extends Kont
case class RetK(x: Var, e: Exp, ρ: Locals) extends Kont
case class FinK(a: Address) extends Kont
