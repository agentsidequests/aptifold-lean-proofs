import MixedRadialFormulas
import PureOddProgram

/-! Arithmetic export of the three mixed forcing coefficients.
The export is a proposal for replay by exact polynomial arithmetic. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open SchwarzschildMixtures.ExactRational SchwarzschildMixtures.PureOddProgram

def rationalConstant (q : Rat) : Formula :=
  if q.den = 1 then .integer q.num else .div (.integer q.num) (.integer q.den)

def coefficients : Quadratic Formula :=
  bareMixedRows rationalConstant Formula.dr .radius .frequency .angular

def exportCoefficients : IO Unit := do
  let make : StateM Graph (Quadratic Nat) := do
    let a ← visit Mixed.coefficients.1
    let b ← visit Mixed.coefficients.2.1
    let c ← visit Mixed.coefficients.2.2
    return (a,b,c)
  let (roots, graph) := make.run {}
  for row in graph.operations do
    IO.println row
  IO.println s!"outputs {roots.1} {roots.2.1} {roots.2.2}"

end SchwarzschildEinstein.PureOdd.Mixed
