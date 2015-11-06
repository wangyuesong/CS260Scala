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

    def main(args: Array[String]) {
      //    val a = args(0);
      val s = scala.io.Source.fromFile(args(0)).mkString
      Parse.getAST(s) match {
        // parsing error: program is not well-formed
        case Left(err) ⇒ println(err)

        // successfully parsed: program is well-formed
        case Right((classTable, ast: Program)) ⇒
          try {
            // throws Illtyped exception if program is not well-typed
            Typechecker.typecheck(ast, classTable)
            // program is well-formed and well-typed; ready to compute
            // fixpoint for collecting semantics
            //
            // NOTE: this version computes the MOP result, i.e., there
            //       is no widening.
            // worklist
            var work = Set[State](initstate(ast))

            // remember set
            val memo = MSet[State]()

            // compute fixpoint
            while (work.nonEmpty) {
              val nextWorkList = work.flatMap(_.next)
              println("Current Worklist size:" + nextWorkList.size)
              work = nextWorkList flatMap (ς ⇒
                {
                  println("-Stmt: " + ς.so)
                  println("-Locals: " + ς.ρ)
                  println("-Heap: " + ς.σ)
                  println("-Konts: " + ς.κs)
                  println()
                  if (ς.fin)
                    // if this is a final state, we don't need to do
                    // anything
                    None
                  else if (ς.so.isEmpty && !ς.κs.head.isInstanceOf[FinK])
                    // we'll skip memorizing intermediate states (i.e.,
                    // states with no statement) just to save space; go
                    // ahead and put such states on the worklist
                    Some(ς)
                  else if (!memo(ς)) {
                    // if the state does have a statement, and we have not
                    // seen it before, memoize it and put it on the
                    // worklist
                    memo += ς
                    Some(ς)
                  } else
                    // the state does have a statement, but we've seen it
                    // before so we don't need to process it again
                    None
                })
            }

            // output abstract values for Print statements: for each
            // Print, join all values for the printed expresion together
            // and output the result. Do this in ascending order of the
            // Print statements' node ids.
            println("TOTAL MEMO COUNT:" + memo.size)
            val out = MMap[Int, Value]()
            memo foreach {
              case ς @ State(Some(print @ Print(e)), _, _, _) ⇒
                out get print.id match {
                  case None ⇒
                    out(print.id) = ς.η(e)

                  case Some(v) ⇒ {
                    out(print.id) = ς.η(e) ⊔ v
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
              Reference.Null
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
              val result = a≠b
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
                  val temp = η(e)
                  Set[State](State(None, ρ + (x -> temp), σ, κs))

                }

              case Update(e1, x, e2) =>
                if (η(e1).is_⊥ || η(e2).is_⊥) Set()
                else η(e1) match {
                  case Reference(as, nil) => Set[State](State(None, ρ, update(σ, as, x, η(e2)), κs))
                  case _                  => Set()
                }
              case Call(x, e, mn, args) =>
                η(e) match {
                  case Reference(as, nil) =>
                    val argVals = args map (η(_))
                    call(x, as, σ, mn, argVals, ρ, κs) map (o => State(None, o._1, o._2, o._3))
                  case _ => Set()
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
                    val kSet = σ.applyK(a).get
                    kSet.map ( k => k.head match{ 
                     case RetK(x, e, ρ1) =>
                        copy(ρ = ρ1 + (x -> η(e)), κs = k.drop(1))
                    })
//                        k match {
//                      case RetK(x, e, ρ1) =>
//                        if (η(e).is_⊥) Set()
//                        else
//                          Set(copy(ρ = ρ1 + (x -> η(e)), κs = k.drop(1)))
//                      case _ => Set()
//                    }
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
