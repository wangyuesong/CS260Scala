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
    // ...

  // section 2.3.3; doesn't take θ because we've factored it out into a global.
  def construct( x:Var, cn:ClassName, vs:Seq[Value], ρ:Locals, σ:Heap, κs:Seq[Kont] ): (Locals, Heap, Seq[Kont]) =
    // ...

  // section 2.3.4
  def defaultvalue( τ:Type ): Value =
    // ...

  // section 2.3.5
  def initstate( p:Program ): State =
    // ...

  // section 2.3.6
  def lookup( as:Set[Address], x:Var, σ:Heap ): Value =
    // ...

  // section 2.3.7
  def toSK( ss:Seq[Stmt] ): Seq[Kont] =
    // ...

  // section 2.3.8
  def update( σ:Heap, as:Set[Address], x:Var, v:Value ): Heap =
    // ...
}
