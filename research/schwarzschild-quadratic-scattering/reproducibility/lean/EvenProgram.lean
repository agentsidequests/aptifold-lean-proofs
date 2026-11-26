import EvenRadialFormulas
import MixedProgram
import Lean.Util.PtrSet

/-! Export the exact arithmetic operations of the same radial rows
that are interpreted by the metric proof. -/
namespace SchwarzschildEinstein.PureOdd.Polar

open SchwarzschildMixtures.ExactRational

def coefficients : Quadratic Formula :=
  bareEvenRows Mixed.rationalConstant Formula.dr .radius .frequency .angular

/-! The IO exporter memoizes already visited objects and keys new nodes
by their operation and child identifiers. Kernel proofs use the formulas
above. An independent exact replay checks what the exporter emits. -/
private unsafe def visit (e : Formula) :
    StateM (Lean.PtrMap Formula Nat × Std.HashMap String Nat × Array String) Nat := do
  if let some id := (← get).1.find? e then
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
  let (objects, ids, operations) ← get
  if let some id := ids[row]? then
    set (objects.insert e id, ids, operations)
    return id
  let id := operations.size
  set (objects.insert e id, ids.insert row id, operations.push row)
  return id

unsafe def exportGraph (rows : Quadratic Formula) : Quadratic Nat × Array String :=
  let build : StateM (Lean.PtrMap Formula Nat × Std.HashMap String Nat × Array String) (Quadratic Nat) := do
    let a ← visit rows.1
    let b ← visit rows.2.1
    let c ← visit rows.2.2
    return (a,b,c)
  let (roots, _, _, operations) := build.run (Lean.mkPtrMap, {}, #[])
  (roots, operations)

unsafe def exportFormulaList (coefficients : List Formula) : List Nat × Array String :=
  let (roots, _, _, operations) := (coefficients.mapM visit).run (Lean.mkPtrMap, {}, #[])
  (roots, operations)

unsafe def exportCoefficients : IO Unit := do
  let (roots, operations) := exportGraph coefficients
  for row in operations do
    IO.println row
  IO.println s!"outputs {roots.1} {roots.2.1} {roots.2.2}"

end SchwarzschildEinstein.PureOdd.Polar
