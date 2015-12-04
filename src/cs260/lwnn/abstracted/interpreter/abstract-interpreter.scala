import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.abstracted.domains._
import cs260.lwnn.abstracted.helpers.Helpers._

import scala.util._
import scala.collection.mutable.{ Set ⇒ MSet, Map ⇒ MMap }

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Abstract interpreter entry point
package cs260.lwnn.abstracted.interpreter {
  object Abstract {
    var count = 0;
    def main(args: Array[String]) {
      //    val a = args(0);
      val s = scala.io.Source.fromFile(args(0)).mkString
      Parse.getAST(s) match {
        // parsing error: program is not well-formed
        case Left(err) ⇒ println(err)

        case Right((classTable, ast: Program)) ⇒
          try {
            Typechecker.typecheck(ast, classTable)
            var work = Set[State](initstate(ast))

            var memo = MMap[Int, State]();

            while (work.nonEmpty) {
              val nextWorkList = work.flatMap(_.next)
              println(count + ":Current Worklist size:" + nextWorkList.size)
              count = count + 1;
//              Thread.sleep(100);
              var memoAdddedCount = 0;
              println("Memo count: " + memo.size);
              nextWorkList.foreach { x => println(x.so) }
              work = nextWorkList flatMap (ς ⇒
                {
                  if (ς.fin)
                    None
                  else if (ς.so.isEmpty) {
                    //Empty and not fink
                    if (!ς.κs.head.isInstanceOf[FinK])
                      Some(ς)
                    //Empty but is fink
                    else {
                      val finKId = ς.κs.head.asInstanceOf[FinK].a.loc
                      //This fink has been seen before
                      memo.get(finKId) match {
                        case Some(s) => {
                          val oldState = memo.get(finKId).get
                          val newState = memo.get(finKId).get.widening(ς)
                          if (oldState.equals(newState))
                            None
                          else {
                            memo = memo + (finKId -> newState)
                            Some(ς)
                          }
                        }
                        //Haven't seen before
                        case None => {
                          memo = memo + (finKId -> ς)
                          Some(ς)
                        }
                      }
                    }
                  } //语句不空，memo中没有这个stmt的id对应的state
                  else {
                    ς.so match {
                      case Some(s) => {
                        if (memo contains s.id) {
                          if (memo(s.id) == memo(s.id).widening(ς))
                            None
                          else {
                            memo(s.id) = memo(s.id).widening(ς)
                            Some(memo(s.id))
                          }
                        } // if the state does have a statement, and we have not
                        else {
                          memo += (s.id -> ς)
                          Some(ς)
                        }
                      }
                      case _ => None
                    }
                  }
                })
            }

            // output abstract values for Print statements: for each
            // Print, join all values for the printed expresion together
            // and output the result. Do this in ascending order of the
            // Print statements' node ids.
            //            println("TOTAL MEMO COUNT:" + memo.size)
            val out = MMap[Int, Value]()
            memo foreach {
              case ς @ (_, State(Some(print @ Print(e)), _, _, _)) ⇒
                out get print.id match {
                  case None ⇒
                    out(print.id) = ς._2.η(e)

                  case Some(v) ⇒ {
                    out(print.id) = ς._2.η(e) ⊔ v
                  }
                }

              case _ ⇒ ()
            }
            out.toSeq.sortBy(_._1).foreach {
              case (id, v) ⇒ println(id + ": " + v)
            }
          } catch {
            // program is not well-typed
            case i: Illtyped ⇒ println(s"TypeError: ${i.msg}")
          }

        case _ ⇒
          sys.error("undefined behavior")
      }
    }
  }

  //——————————————————————————————————————————————————————————————————————————————
  // State, transition rules, and η
  //
  // Note: Any undefined behavior of the program (i.e., that would
  // result in a sys.error in the concrete semantics) should result in
  // next returning an empty set of States in the abstract version. This
  // includes if η returns a ⊥ value.

  case class State(so: Option[Stmt], ρ: Locals, σ: Heap, κs: Seq[Kont]) {
    override def toString() = {
      val stmt = "Statement:\n" + so + "\n"
      var locals = "Locals:\n"
      ρ.x2v.foreach(m => locals = locals + m._1.name + ":" + m._2 + "\n")
      var heap = "Heap:\n OMap:\n"
      σ.a2o.foreach(x => heap = heap + x._1 + ":" + x._2 + "\n")
      heap = heap + "KMap:\n"
      σ.a2k.foreach(x => heap = heap + x._1 + ":" + x._2 + "\n")
      stmt + locals + heap

    }
    //两个state进行widen操作，首先stmt肯定相同，不需要widen，Locals中的所有var值join，遇到reference
    def widening(s: State) = {
      State(so, ρ.widening(s.ρ), σ.widening(s.σ), κs)
    }

    // is this a final state (i.e., the program has terminated)?
    def fin: Boolean =
      so.isEmpty && κs.isEmpty

    // we define η here so that we have access to ρ and σ without
    // needing to pass them in as parameters.
    def η(e: Exp): Value =
      e match {
        case Nums(ns) =>
          ℤ.α(ns)
        case Bools(bs) =>
          Bool.α(bs)
        case Strs(ss) =>
          Str.α(ss)
        case Nulls() =>
          Reference.Null
        case x: Var =>
          //Return a value,could be Z,Bool,Str,Reference
          ρ(x)
        case Access(e: Exp, x: Var) =>
          η(e) match {
            case Reference(sa, false) =>
              lookup(sa, x, σ)
            case _ =>
              Reference.⊥
          }
        case Binop(op, e1, e2) =>
          op match {
            case ⌜+⌝ => η(e1) + η(e2)
            case ⌜−⌝ => η(e1) − η(e2)
            case ⌜×⌝ => η(e1) × η(e2)
            case ⌜÷⌝ => η(e1) ÷ η(e2)
            case ⌜<⌝ ⇒ η(e1) < η(e2)
            case ⌜≤⌝ ⇒ η(e1) ≤ η(e2)
            case ⌜≈⌝ ⇒ η(e1) ≈ η(e2)
            case ⌜≠⌝ ⇒
              {
                val a = η(e1)
                val b = η(e2)
                val result = a ≠ b
                result
              }
            case ⌜∧⌝ ⇒ η(e1) ∧ η(e2)
            case ⌜∨⌝ ⇒ η(e1) ∨ η(e2)
          }
      }

    // the state transition relation.
    def next: Set[State] =
      {
        so match {
          case Some(s) =>
            s match {
              case Print(e: Exp) => {
                Set(copy(so = None))
              }
              case Assign(x, e) =>
                {
                  if (η(e).is_⊥) Set()
                  Set[State](State(None, ρ + (x -> η(e)), σ, κs))

                }

              case Update(e1, x, e2) =>
                if (η(e1).is_⊥ || η(e2).is_⊥) Set()
                else η(e1) match {
                  case Reference(as, nil) => Set[State](State(None, ρ, update(σ, as, x, η(e2)), κs))
                  case _                  => Set()
                }
              //if(..)
              //   X= new A();
              //                else
              //                  X = new B();
              //                X.s();

              case Call(x, e, mn, args) =>
                {
                  η(e) match {
                    case Reference(as, false) => {
                      val argVals = args map (η(_))
                      val tempVal = call(x, as, σ, mn, argVals, ρ, κs) map (o => State(None, o._1, o._2, o._3))
                      tempVal
                    }
                    case _ => Set()
                  }
                }
              case New(x, cn, args) =>
                {
                  val argVals = args map (η(_))
                  val tmp = construct(x, cn, argVals, ρ, σ, κs)
                  Set(State(None, tmp._1, tmp._2, tmp._3))
                }
              case If(e, tb, fb) => {
                η(e) match {
                  case b: Bool => {
                    if (b.is_⊥) Set()
                    else b.bs flatMap (_ match {
                      case true  => Some(copy(so = None, κs = toSK(tb) ++ κs))
                      case false => Some(copy(so = None, κs = toSK(fb) ++ κs))
                    })
                  }
                  case _ => Set()
                }
              }
              case While(e, body) =>
                η(e) match {
                  case b: Bool => {
                    if (b.is_⊥) Set()
                    else b.bs flatMap (_ match {
                      case true  => Some(copy(so = None, κs = toSK(body) ++ Seq(WhileK(e, body)) ++ κs))
                      case false => Some(copy(so = None))
                    })
                  }
                  case _ => Set()
                }
            }
          case None => {
            κs.size match {
              case 0 => Set()
              case _ =>
                κs.head match {
                  case FinK(a) => {
                    val kSet = σ.applyK(a)
                    kSet.map(k => k.head match {
                      case RetK(x, e, ρ1) =>
                        copy(ρ = ρ1 + (x -> η(e)), κs = k.drop(1))
                    })
                  }
                  case StmtK(s1) =>
                    Set(copy(so = Some(s1), κs = κs.tail))
                  case WhileK(e, body) =>
                    η(e) match {
                      case b: Bool => {
                        if (b.is_⊥) Set()
                        else b.bs flatMap (_ match {
                          case true  => Some(copy(κs = toSK(body) ++ κs))
                          case false => Some(copy(κs = κs.tail))
                        })
                      }
                      case _ => Set()
                    }
                }
            }

          }
        }
      }
  }

}
