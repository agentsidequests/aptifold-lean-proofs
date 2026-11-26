import ExactRationalData
import PureOddFormulas
import Std.Data.HashMap

/-! Export the arithmetic operations of the same formulas used in the
proof. This export proposes witnesses. The kernel checks those witnesses
against the formulas and their rational-function interpretation. -/
namespace SchwarzschildMixtures.PureOddProgram

open SchwarzschildEinstein.PureOdd ExactRational

def coefficients : Quadratic Formula :=
  bareForcing Formula.dr .radius .frequency .angular

structure Graph where
  identifiers : Std.HashMap Formula Nat := {}
  operations : Array String := #[]

def visit (e : Formula) : StateM Graph Nat := do
  if let some id := (← get).identifiers[e]? then
    return id
  let row ← match e with
    | .integer z => pure s!"integer {z}"
    | .radius => pure "radius"
    | .frequency => pure "frequency"
    | .angular => pure "angular"
    | .add a b => pure s!"add {← visit a} {← visit b}"
    | .mul a b => pure s!"mul {← visit a} {← visit b}"
    | .div a b => pure s!"div {← visit a} {← visit b}"
    | .neg a => pure s!"neg {← visit a}"
    | .dr a => pure s!"dr {← visit a}"
  let id := (← get).operations.size
  modify fun g => { identifiers := g.identifiers.insert e id, operations := g.operations.push row }
  return id

def graph : Quadratic Nat × Graph :=
  let run : StateM Graph (Quadratic Nat) := do
    let a ← visit coefficients.1
    let b ← visit coefficients.2.1
    let c ← visit coefficients.2.2
    return (a,b,c)
  run.run {}

end SchwarzschildMixtures.PureOddProgram

def main : IO Unit := do
  let (roots, graph) := SchwarzschildMixtures.PureOddProgram.graph
  for row in graph.operations do
    IO.println row
  IO.println s!"outputs {roots.1} {roots.2.1} {roots.2.2}"
