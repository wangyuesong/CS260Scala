import cs260.lwnn.syntax._
import cs260.lwnn.util._
import cs260.lwnn.abstracted.domains._
import cs260.lwnn.abstracted.helpers.Helpers._

import scala.util._
import scala.collection.mutable.{ Set ⇒ MSet, Map ⇒ MMap }

import TypeAliases._

//——————————————————————————————————————————————————————————————————————————————
// Abstract interpreter entry point

object Abstract {
  import cs260.lwnn.abstracted.interpreter.State

  def main( args:Array[String] ) {
    Parse.getAST( scala.io.Source.fromFile(args(0)).mkString ) match {
      // parsing error: program is not well-formed
      case Left(err) ⇒ println(err)

      // successfully parsed: program is well-formed
      case Right((classTable, ast:Program)) ⇒
        try {
          // throws Illtyped exception if program is not well-typed
          Typechecker.typecheck(ast, classTable)

          // program is well-formed and well-typed; ready to compute
          // fixpoint for collecting semantics
          //
          // NOTE: this version computes the MOP result, i.e., there
          //       is no widening.

          // worklist
          var work = Set[State]( initstate(ast) )

          // remember set
          val memo = MSet[State]()

          // compute fixpoint
          while ( work.nonEmpty ) {
            work = work.flatMap( _.next ).flatMap( ς ⇒
              if ( ς.fin )
                // if this is a final state, we don't need to do
                // anything
                None 
              else if ( ς.so.isEmpty && !ς.κs.head.isInstanceOf[FinK] )
                // we'll skip memoizing intermediate states (i.e.,
                // states with no statement) just to save space; go
                // ahead and put such states on the worklist
                Some(ς)
              else if ( !memo(ς) ) {
                // if the state does have a statement, and we have not
                // seen it before, memoize it and put it on the
                // worklist
                memo += ς
                Some(ς)
              }
              else
                // the state does have a statement, but we've seen it
                // before so we don't need to process it again
                None
            )
          }

          // output abstract values for Print statements: for each
          // Print, join all values for the printed expresion together
          // and output the result. Do this in ascending order of the
          // Print statements' node ids.
          val out = MMap[Int, Value]()
          memo foreach {
            case ς @ State(Some(print @ Print(e)), _, _, _) ⇒
              out get print.id match {
                case None ⇒
                  out(print.id) = ς.η(e)

                case Some(v) ⇒
                  out(print.id) = ς.η(e) ⊔ v
              }

            case _ ⇒ ()
          }
          out.toSeq.sortBy(_._1).foreach {
            case (id, v) ⇒ println(id + ": " + v)
          }
        }
        catch {
          // program is not well-typed
          case i:Illtyped ⇒ println(s"TypeError: ${i.msg}")
        }

      case _ ⇒
        sys.error("undefined behavior")
    }
  }
}

package cs260.lwnn.abstracted.interpreter {

//——————————————————————————————————————————————————————————————————————————————
// State, transition rules, and η
//
// Note: Any undefined behavior of the program (i.e., that would
// result in a sys.error in the concrete semantics) should result in
// next returning an empty set of States in the abstract version. This
// includes if η returns a ⊥ value.

case class State( /* ... */ ) {
  // is this a final state (i.e., the program has terminated)?
  def fin: Boolean =
    // ...

  // we define η here so that we have access to ρ and σ without
  // needing to pass them in as parameters.
  def η( e:Exp ): Value =
    // ...

  // the state transition relation.
  def next: Set[State] =
    // ...
}
