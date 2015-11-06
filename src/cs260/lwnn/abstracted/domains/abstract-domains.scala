package cs260.lwnn.abstracted.domains

import scala.annotation.elidable
import scala.annotation.elidable.ASSERTION
import scala.annotation.migration
import scala.math.BigInt.int2bigInt

import cs260.lwnn.syntax.Exp
import cs260.lwnn.syntax.Method
import cs260.lwnn.syntax.Stmt
import cs260.lwnn.syntax.TypeAliases.ClassName
import cs260.lwnn.syntax.TypeAliases.MethodName
import cs260.lwnn.syntax.Var
import cs260.lwnn.util.Type

//——————————————————————————————————————————————————————————————————————————————
// ClassDefs
//
// the class definitions are invariant, so we can factor them out into
// one global version rather than having one per state as in the
// formal semantics

case object θ {
  type FieldMap = Map[Var, Type]
  type MethodMap = Map[MethodName, Method]
  val topClass = ("TopClass" -> (Map[Var, Type](), Map[MethodName, Method]()))

  // ... (same as for the concrete semantics)
  var classdefs = Map[ClassName, (FieldMap, MethodMap)](topClass)

  def apply(cn: ClassName): (FieldMap, MethodMap) = {
    classdefs(cn)
  }

  def fieldMap(cn: ClassName): FieldMap = {
    classdefs(cn)._1
  }

  def methodMap(cn: ClassName): MethodMap = {
    classdefs(cn)._2
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Locals

case class Locals(x2v: Map[Var, Value]) {
  // ...
  def apply(x: Var): Value = {
    x2v(x)
  }

  def +(xv: (Var, Value)): Locals = {
//    assert(x2v contains xv._1)
    //Update or add new
    Locals(x2v + xv)
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
case class Heap(oMap: Map[Address, Object], kMap: Map[Address, Set[Seq[Kont]]]) {

  def applyO(a: Address): Option[Object] = {
    oMap.get(a)
  }
  def applyK(a: Address): Option[Set[Seq[Kont]]] = {
    kMap.get(a)
  }

  def addO(ao: (Address, Object)): Heap = {
    //Update 
    //如果Heap中Address对应的object已经有值，求union
   val returnHeap = if (oMap contains ao._1) 
      Heap(oMap + (ao._1 -> ao._2 ⊔ oMap(ao._1)), kMap)
    //否则新建
    else Heap(oMap + ao, kMap)
    returnHeap
  }
  
  //Add konts
  def addK(ak: (Address, Seq[Kont])): Heap = {
    kMap.get(ak._1) match{
      case Some(prevStack) => Heap(oMap, kMap + (ak._1-> (prevStack + ak._2)))
      case None => Heap(oMap, kMap + (ak._1-> Set(ak._2)))
    }
    
  }

}
//——————————————————————————————————————————————————————————————————————————————
// Value
//
// NOTE: the type system disallows many operations on disparate value
// types (including ⊔), but we need to define them in the
// implementation anyway or the compiler will complain. We'll just
// have them return a ⊥ value.

sealed abstract class Value {
  def is_⊥ : Boolean = sys.error("undefined behavior")
  def ⊔(v: Value): Value = sys.error("undefined behavior")
  def +(v: Value): Value = sys.error("undefined behavior")
  def −(v: Value): Value = sys.error("undefined behavior")
  def ×(v: Value): Value = sys.error("undefined behavior")
  def ÷(v: Value): Value = sys.error("undefined behavior")
  def <(v: Value): Value = sys.error("undefined behavior")
  def ≤(v: Value): Value = sys.error("undefined behavior")
  def ∧(v: Value): Value = sys.error("undefined behavior")
  def ∨(v: Value): Value = sys.error("undefined behavior")
  //???
  def ≈(v: Value): Value = sys.error("undefined behavior")
  def ≠(v: Value): Value = sys.error("undefined behavior")
}

// we'll use the {+,0,−} abstract domain with the following lattice:
// 
//      ⊤
//     /|\
//    − 0 +
//     \|/
//      ⊥
//
sealed abstract class ℤ extends Value {
  //Join
  override def ⊔(a: Value): ℤ = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        //Anything join TOP result in TOP
        case (_, ZTOP)      => ZTOP

        //Anything join bottom result in itself
        case (a, ZBOTTOM)   => a
        case (ZBOTTOM, a)   => a

        //Join itself
        case (ZPOS, ZPOS)   => ZPOS
        case (ZZERO, ZZERO) => ZZERO
        case (ZNEG, ZNEG)   => ZNEG

        //Otherwise just get top
        case _              => ZTOP
      }
    case _ => sys.error("undefined behavior: not joinable")
  }

  override def is_⊥ : Boolean = this match {
    case ZBOTTOM => true
    case _       => false
  }

  override def +(a: Value): ℤ = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        case (ZBOTTOM, _)   => ZBOTTOM
        case (_, ZBOTTOM)   => ZBOTTOM
        case (ZTOP, _)      => ZTOP
        case (_, ZTOP)      => ZTOP
        case (ZPOS, ZPOS)   => ZPOS
        case (ZPOS, ZNEG)   => ZTOP
        case (ZPOS, ZZERO)  => ZPOS
        case (ZNEG, ZPOS)   => ZTOP
        case (ZNEG, ZNEG)   => ZNEG
        case (ZNEG, ZZERO)  => ZNEG
        case (ZZERO, ZPOS)  => ZPOS
        case (ZZERO, ZNEG)  => ZNEG
        case (ZZERO, ZZERO) => ZZERO
      }
    case _ => sys.error("undefined behavior")
  }

  override def −(a: Value): ℤ = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        case (ZBOTTOM, _)   => ZBOTTOM
        case (_, ZBOTTOM)   => ZBOTTOM
        case (ZTOP, _)      => ZTOP
        case (_, ZTOP)      => ZTOP
        case (ZPOS, ZPOS)   => ZTOP
        case (ZPOS, ZNEG)   => ZPOS
        case (ZPOS, ZZERO)  => ZPOS
        case (ZNEG, ZPOS)   => ZNEG
        case (ZNEG, ZNEG)   => ZTOP
        case (ZNEG, ZZERO)  => ZNEG
        case (ZZERO, ZPOS)  => ZNEG
        case (ZZERO, ZNEG)  => ZPOS
        case (ZZERO, ZZERO) => ZZERO
      }
    case _ => sys.error("undefined behavior")
  }

  override def ×(a: Value): ℤ = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {

        case (ZBOTTOM, _) => ZBOTTOM
        case (_, ZBOTTOM) => ZBOTTOM
        case (ZTOP, _)    => ZTOP
        case (_, ZTOP)    => ZTOP
        case (_, ZZERO)   => ZZERO
        case (ZZERO, _)   => ZZERO

        case (ZPOS, ZPOS) => ZPOS
        case (ZPOS, ZNEG) => ZNEG
        case (ZNEG, ZPOS) => ZNEG
        case (ZNEG, ZNEG) => ZPOS

      }
    case _ => sys.error("undefined behavior")
  }

  override def ÷(z: Value): ℤ = {
    z match{
      case ZBOTTOM => ZBOTTOM
      case ZTOP => {
        this match {
          case ZZERO => ZZERO
          //Zero divided by Top return TOP
          case _ => ZTOP
        }
      }
      case ZNEG =>{
        this match{
          case ZBOTTOM => ZBOTTOM
          case ZTOP => ZTOP
          case ZNEG => ZPOS
          case ZZERO => ZZERO
          case ZPOS => ZNEG
        }
      }
      case ZZERO =>{
        this match{
          case ZBOTTOM => ZBOTTOM
          case ZTOP => ZTOP
          case ZNEG => ZBOTTOM
          case ZZERO => ZBOTTOM
          case ZPOS => ZBOTTOM
        }
      }
      case ZPOS =>{
        this match{
          case ZBOTTOM => ZBOTTOM
          case ZTOP => ZTOP
          case ZNEG => ZNEG
          case ZZERO => ZZERO
          case ZPOS => ZPOS
        }
      }
      case _ => sys.error("undefined behavior")
    }
  }

  override def <(a: Value): Bool = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        case (ZBOTTOM, _)   => Bool.⊥
        case (_, ZBOTTOM)   => Bool.⊥
        case (ZTOP, _)      => Bool.⊤
        case (_, ZTOP)      => Bool.⊤
        //POS
        case (ZPOS, ZPOS)   => Bool.⊤
        case (ZPOS, ZNEG)   => Bool.False
        case (ZPOS, ZZERO)  => Bool.False
        //NEG
        case (ZNEG, ZPOS)   => Bool.True
        case (ZNEG, ZNEG)   => Bool.⊤
        case (ZNEG, ZZERO)  => Bool.True
        //ZERO
        case (ZZERO, ZPOS)  => Bool.True
        case (ZZERO, ZNEG)  => Bool.False
        case (ZZERO, ZZERO) => Bool.False
      }
    case _ => sys.error("undefined behavior")
  }

  override def ≤(a: Value): Bool = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        case (ZBOTTOM, _)   => Bool.⊥
        case (_, ZBOTTOM)   => Bool.⊥
        case (ZTOP, _)      => Bool.⊤
        case (_, ZTOP)      => Bool.⊤
        //POS
        case (ZPOS, ZPOS)   => Bool.⊤
        case (ZPOS, ZNEG)   => Bool.False
        case (ZPOS, ZZERO)  => Bool.False
        //NEG
        case (ZNEG, ZPOS)   => Bool.True
        case (ZNEG, ZNEG)   => Bool.⊤
        case (ZNEG, ZZERO)  => Bool.True
        //ZERO
        case (ZZERO, ZPOS)  => Bool.True
        case (ZZERO, ZNEG)  => Bool.False
        case (ZZERO, ZZERO) => Bool.True
      }
    case _ => sys.error("undefined behavior")
  }

  override def ≈(a: Value): Bool = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        case (ZBOTTOM, _)   => Bool.⊥
        case (_, ZBOTTOM)   => Bool.⊥
        case (ZTOP, _)      => Bool.⊤
        case (_, ZTOP)      => Bool.⊤
        //POS
        case (ZPOS, ZPOS)   => Bool.⊤
        case (ZPOS, ZNEG)   => Bool.False
        case (ZPOS, ZZERO)  => Bool.False
        //NEG
        case (ZNEG, ZPOS)   => Bool.False
        case (ZNEG, ZNEG)   => Bool.⊤
        case (ZNEG, ZZERO)  => Bool.False
        //ZERO
        case (ZZERO, ZPOS)  => Bool.False
        case (ZZERO, ZNEG)  => Bool.False
        case (ZZERO, ZZERO) => Bool.True
      }
    case _ => sys.error("undefined behavior")
  }

  override def ≠(a: Value): Bool = (this, a) match {
    case (a: ℤ, b: ℤ) =>
      (a, b) match {
        case (ZBOTTOM, _)   => Bool.⊥
        case (_, ZBOTTOM)   => Bool.⊥
        case (ZTOP, _)      => Bool.⊤
        case (_, ZTOP)      => Bool.⊤
        //POS
        case (ZPOS, ZPOS)   => Bool.⊤
        case (ZPOS, ZNEG)   => Bool.True
        case (ZPOS, ZZERO)  => Bool.True
        //NEG
        case (ZNEG, ZPOS)   => Bool.True
        case (ZNEG, ZNEG)   => Bool.⊤
        case (ZNEG, ZZERO)  => Bool.True
        //ZERO
        case (ZZERO, ZPOS)  => Bool.True
        case (ZZERO, ZNEG)  => Bool.True
        case (ZZERO, ZZERO) => Bool.False
      }
    case _ => sys.error("undefined behavior")
  }
}

// ...
case object ZPOS extends ℤ
case object ZNEG extends ℤ
case object ZZERO extends ℤ
case object ZTOP extends ℤ
case object ZBOTTOM extends ℤ

object ℤ {
  val ⊤ = ZTOP
  val ⊥ = ZBOTTOM
  val NEG = ZNEG
  val POS = ZPOS
  val ZERO = ZZERO

  def α(ns: Set[BigInt]): ℤ =
    {
      val t = ns map {x:BigInt => if (x>0) POS else if (x==0) ZERO else NEG}
    t.size match {
      case 0 => ZBOTTOM
      case 1 => t.head
      case _ => ZTOP
    }
    }
  def α(n: BigInt): ℤ =
    α(Set(n))
}

// we'll use the (𝒫({true, false}), ⊆) abstract domain.
case class Bool(bs: Set[Boolean]) extends Value {
  // ...
  override def ∧(v: Value): Bool = (this, v) match {
    case (a: Bool, b: Bool) => (a, b) match {
      case (Bool.⊥, _)              => Bool.⊥
      case (_, Bool.⊥)              => Bool.⊥
      case (Bool.⊤, _)              => Bool.⊤
      case (_, Bool.⊤)              => Bool.⊤
      case (Bool.True, Bool.False)  => Bool.False
      case (Bool.True, Bool.True)   => Bool.True
      case (Bool.False, Bool.False) => Bool.False
      case (Bool.False, Bool.True)  => Bool.False
    }
  }

  override def ∨(v: Value): Bool = (this, v) match {
    case (a: Bool, b: Bool) => (a, b) match {
      case (Bool.⊥, _)              => Bool.⊥
      case (_, Bool.⊥)              => Bool.⊥
      case (Bool.⊤, _)              => Bool.⊤
      case (_, Bool.⊤)              => Bool.⊤
      case (Bool.True, Bool.False)  => Bool.True
      case (Bool.True, Bool.True)   => Bool.True
      case (Bool.False, Bool.False) => Bool.False
      case (Bool.False, Bool.True)  => Bool.True
    }
  }

  override def ≈(v: Value): Bool = (this, v) match {
    case (a: Bool, b: Bool) => (a, b) match {
      case (Bool.⊥, _)              => Bool.⊥
      case (_, Bool.⊥)              => Bool.⊥
      case (Bool.⊤, _)              => Bool.⊤
      case (_, Bool.⊤)              => Bool.⊤
      case (Bool.True, Bool.False)  => Bool.False
      case (Bool.True, Bool.True)   => Bool.True
      case (Bool.False, Bool.False) => Bool.True
      case (Bool.False, Bool.True)  => Bool.False
    }
    case _ => sys.error("undefined behavior: bool not comparable")
  }

  override def ≠(v: Value): Value = (this, v) match {
    case (a: Bool, b: Bool) => (a, b) match {
      case (Bool.⊥, _)              => Bool.⊥
      case (_, Bool.⊥)              => Bool.⊥
      case (Bool.⊤, _)              => Bool.⊤
      case (_, Bool.⊤)              => Bool.⊤
      case (Bool.True, Bool.False)  => Bool.True
      case (Bool.True, Bool.True)   => Bool.False
      case (Bool.False, Bool.False) => Bool.False
      case (Bool.False, Bool.True)  => Bool.True
    }
    case _ => sys.error("undefined behavior: bool not comparable")
  }

  override def ⊔(a: Value): Bool = (this, a) match {
    case (a: Bool, b: Bool) =>
      (a, b) match {
        case (Bool.⊤, _)              => Bool.⊤
        case (_, Bool.⊤)              => Bool.⊤

        case (a, Bool.⊥)              => a
        case (Bool.⊥, a)              => a
        //Otherwise just get top
        case (Bool.True, Bool.False)  => Bool.⊤
        case (Bool.True, Bool.True)   => Bool.True
        case (Bool.False, Bool.False) => Bool.False
        case (Bool.False, Bool.True)  => Bool.⊤
      }
    case _ => sys.error("undefined behavior: not joinable")
  }
  override def is_⊥ : Boolean = this match {
    case Bool.⊥ => true
    case _      => false
  }

  override def toString =
    if (bs.size == 1) bs.head.toString
    else "{true, false}"
}

object Bool {
  val ⊤ = Bool(Set[Boolean](true, false))
  val ⊥ = Bool(Set[Boolean]())
  val True = Bool(Set[Boolean](true))
  val False = Bool(Set[Boolean](false))
  def α(bs: Set[Boolean]): Bool =
     // ...
    bs.size match {
      case 0 => this.⊥
      case 1 => bs.head match {
        case true => this.True
        case false => this.False
      }
      case 2 => this.⊤
    }
  
  def α(b: Boolean): Bool =
    α(Set[Boolean](b))
}

// for strings we'll use the {⊥,⊤} domain s.t. ⊥ means no string and ⊤
// means any string, so the ordering is ⊥ ⊑ ⊤.

sealed abstract class Str extends Value {
  override def is_⊥ : Boolean = this match {
    case Str.⊥ => true
    case _     => false
  }

  override def ⊔(v: Value): Str = (this, v) match {
    case (a: Str, b: Str) => (a, b) match {
      case (a, SBOTTOM) => a
      case (SBOTTOM, a) => a
      case (_, _)       => STOP
    }
    case _ => sys.error("undefined behavior")
  }

  override def +(v: Value): Str = (this, v) match {
    case (a: Str, b: Str) => (a, b) match {
      case (STOP, STOP) => STOP
      case _            => SBOTTOM
    }
    case _ => sys.error("undefined behavior")
  }

  override def <(v: Value): Bool = (this, v) match {
    case (a: Str, b: Str) => (a, b) match {
      case (STOP, STOP) => Bool.⊤ //Can be true or false
      case _            => Bool.⊥
    }
    case _ => sys.error("undefined behavior")
  }

  override def ≤(v: Value): Bool = (this, v) match {
    case (a: Str, b: Str) => (a, b) match {
      case (STOP, STOP) => Bool.⊤ //Can be true or false
      case _            => Bool.⊥
    }
    case _ => sys.error("undefined behavior")
  }

  override def ≈(v: Value): Value = (this, v) match {
    case (a: Str, b: Str) => (a, b) match {
      case (STOP, STOP) => Bool.⊤ //Can be true or false
      case _            => Bool.⊥
    }
    case _ => sys.error("undefined behavior")
  }
  override def ≠(v: Value): Value = (this, v) match {
    case (a: Str, b: Str) => (a, b) match {
      case (STOP, STOP) => Bool.⊤ //Can be true or false
      case _            => Bool.⊥
    }
    case _ => sys.error("undefined behavior")
  }
}
// ...
case object STOP extends Str
case object SBOTTOM extends Str

object Str {
  val ⊤ = STOP
  val ⊥ = SBOTTOM

  def α(strs: Set[String]): Str = {
    // ...
    val ss = strs map { s => if (s.length > 0) STOP else SBOTTOM }
    if (ss.contains(STOP)) 
      STOP
    else 
      SBOTTOM
  }

  def α(s: String): Str =
    Str.α(Set[String](s))

}

// for convenience we'll keep a set of addresses and separately a
// boolean indicating whether the reference could also be Null.
case class Reference(as: Set[Address], nil: Boolean = false) extends Value {

  override def is_⊥ : Boolean = {
    this == Reference.⊥
  }

  override def ⊔(v: Value): Reference = {
    v match {
      case v: Reference => Reference(as ++ v.as, nil || v.nil)
      case _            => sys.error("undefined behavior")
    }
  }

 override def ≈ (v: Value) : Bool = {
    (this,v) match {
      case (Reference.Null,Reference.Null) => Bool.True
      case (Reference(as1,false),Reference(as2,false)) =>{
        if (as1.toList.length == 1 && as2.toList.length==1 && as1==as2) Bool.True
        else if ((as1 & as2).toList.length>0) Bool.⊤
        else Bool.False
      }
      case (Reference(as1,true),Reference(as2,false)) =>{
        if ((as1 & as2).toList.length>0) Bool.⊤
        else Bool.False
      }
      case (Reference(as1,false),Reference(as2,true)) =>{
        if ((as1 & as2).toList.length>0) Bool.⊤
        else Bool.False
      }
      case (Reference(_,true),Reference(_,true)) =>{
        Bool.⊤
      }
      case _ => sys.error("undefined behavior")
    }
  }

  override def ≠ (v: Value) : Bool = {
    (this,v) match {
      case (Reference.Null,Reference.Null) => Bool.False
      case (Reference(as1,false),Reference(as2,false)) =>{
        if (as1.toList.length==1 && as2.toList.length==1 && as1==as2) Bool.False
        else if ((as1 & as2).toList.length>0) Bool.⊤
        else Bool.True
      }
      case (Reference(as1,true),Reference(as2,false)) =>{
        if ((as1 & as2).toList.length>0) Bool.⊤
        else Bool.True
      }
      case (Reference(as1,false),Reference(as2,true)) =>{
        if ((as1 & as2).toList.length>0) Bool.⊤
        else Bool.True
      }
      case (Reference(_,true),Reference(_,true)) =>{
        Bool.⊤
      }
      case _ => sys.error("undefined behavior")
    }
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
  val ⊥ = Reference(Set[Address](), false)
  val Null = Reference(Set[Address](), true)

  def apply(a: Address): Reference = {
    Reference(Set[Address](a), false)
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
    val returnValue = Object(cn, flds map { case (k, v) => (k, o(k) ⊔ v) })
    returnValue;
  }

  def apply(x: Var): Value =
    flds(x)

  def +(xv: (Var, Value)): Object =
    Object(cn, flds + xv)
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

sealed abstract class Kont
case class StmtK(s: Stmt) extends Kont
case class WhileK(e: Exp, ss: Seq[Stmt]) extends Kont
case class RetK(x: Var, e: Exp, ρ: Locals) extends Kont
case class FinK(a: Address) extends Kont
