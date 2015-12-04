package cs260.lwnn.abstracted.helpers

import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.abstracted.domains._
import cs260.lwnn.abstracted.interpreter.State

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Helper functions

object Helpers {
  // section 2.3.2; doesn't take θ because we've factored it out into a global.
  def call( x:Var, as:Set[Address], σ:Heap, mn:MethodName, vs:Seq[Value], ρ:Locals, κs:Seq[Kont] ): Set[(Locals, Heap, Seq[Kont])] =
  {
    //Set[Address, Method]
    val am = as map { a => (a, θ(σ.applyO(a).cn)._2.get(mn).get)}
    var returnValue : Set[(Locals, Heap, Seq[Kont])] = Set[(Locals, Heap, Seq[Kont])]() 
    am.foreach(a => {
      val self = List((Var("self")->Reference(Set(a._1),false)))
      val assginedParams = (a._2.params.tail.map{a=>a.x}.toList zip (vs))
      val defaultParams = (a._2.params.drop(vs.length + 1) map { p => (p.x->defaultvalue(p.τ))})
      val localsa = Locals((self ++ assginedParams ++ defaultParams).toMap)
      val σa = σ.addK((Address(a._2.id)-> ((Seq[Kont](RetK(x, a._2.rete,ρ)) ++ κs) ) ))
      val κsa =  toSK(a._2.body) :+ FinK(Address(a._2.id))
      val addedVal =  (localsa,σa,κsa);
      returnValue = returnValue + addedVal
    })
     returnValue
  }
  // section 2.3.3; doesn't take θ because we've factored it out into a global.
  def construct( x:Var, cn:ClassName, vs:Seq[Value], ρ:Locals, σ:Heap, κs:Seq[Kont] ): (Locals, Heap, Seq[Kont]) =
  {
    val initMethod = θ(cn)._2(cn)
    //Two address
    //生成a的时候判断一下var是否在local里，在的话就不生成新的id
   
    val top_a = Address(x.id)
    val top_a_k = Address(initMethod.id)
    
    //These are setting default values for fields
    val fields =  θ(cn)._1
    val objectDefaultFieldValues = fields.map(p=> (p._1 -> defaultvalue(p._2)))
    
    val o = Object(cn, objectDefaultFieldValues)
    //These are for new local
    //这一句有问题
    val self = List((Var("self")->Reference(Set(top_a),false)))
    val assignedParams = θ(cn)._2(cn).params.tail.map(a=>a.x).toList zip (vs)
    val defaultParams = θ(cn)._2(cn).params.drop(assignedParams.length + 1) map (p=> (p.x->defaultvalue(p.τ)))
    
    val ρ1 = Locals((self ++ assignedParams ++ defaultParams).toMap)
    val σ1 = σ.addO(top_a, o)
    val σ2 = σ1.addK((top_a_k, List(RetK(x,Var("self"),ρ)) ++ κs ))
    val top_k1 = (toSK(initMethod.body) :+ FinK(top_a_k) )  
    (ρ1, σ2,  top_k1)
  }
  // section 2.3.4
  def defaultvalue( τ:Type ): Value =
  {
    τ match{
    case IntT => ℤ.α(0)
    case BoolT => Bool.α(false)
    case StrT => Str.α(Set[String](""))
    case _ => Reference.Null
    }
  }

  // section 2.3.5
def initstate(p: Program): State = {
      var σ = Heap(Map[Address, Object](),Map[Address,Set[Seq[Kont]]]())
      var ρ = Locals(Map[Var, Value]())
      var κs = Seq[Kont]()
      var classSeq = p.classes
      //Not fold left
      classSeq.foreach { c =>  θ.classdefs = θ.classdefs + (c.cn -> initclass(c)) }
      val firstClass = classSeq(0)
      val cn = firstClass.cn
      val fldTypes = θ(cn)._1;
      var flds = Map[Var, Value]()
      fldTypes.foreach { f => flds = flds + (f._1 -> defaultvalue(f._2)) }
      val o = Object(cn, flds)
      //NOT SURE
      val a = Address(0)
      σ = σ.addO(a->o)
      //初始化构造函数的参数们
      θ(cn)._2.get(cn) match {
        case Some(m) =>
          {
            κs = κs ++ toSK(m.body)
            val params = m.params.tail
            params.foreach { x => ρ = ρ + (x.x, defaultvalue(x.τ)) }
            //NOT SURE
            ρ = ρ + (Var("self") -> Reference(Set[Address](a),false));
          }
        case None =>
          sys.error("undefined behavoir")
      }
      
      State(None, ρ, σ, κs)
    }

  def initclass(c: Class): (θ.FieldMap, θ.MethodMap) =
      {
        //从θ中找到父类的各种定义
             val returnValue= (θ(c.supercn)._1 ++ (c.fields map { x: Decl => (x.x, x.τ) }).toMap, θ(c.supercn)._2 ++ (c.methods map { m: Method => (m.mn, m) }).toMap)
             returnValue
      }


//  // section 2.3.6
  def lookup( sa:Set[Address], x:Var, σ:Heap ): Value =
  {
       var valList = sa.map { a => σ.applyO(a) }.map{o => o(x)}
       valList.reduceLeft(_ ⊔ _)
  }
       
  // section 2.3.7
  def toSK(ss: Seq[Stmt]): Seq[Kont] =
      ss map (StmtK(_))

  // section 2.3.8
  def update( σ:Heap, as:Set[Address], x:Var, v:Value ): Heap ={
    	var σ1 = σ
    	for(a<-as)
      {
		    var o = σ.applyO(a) 
		    var xv = (x, v ⊔ o.flds(x))
		    o = o + xv
		    σ1 = σ1.addO(a, o)
      }
    	//as.foreach(a => val o = (σ(a)) o._2(x) = (v ⊔ σ(a)._2(x)) σ = σ + (a, o))
      σ1
  }
  
}
