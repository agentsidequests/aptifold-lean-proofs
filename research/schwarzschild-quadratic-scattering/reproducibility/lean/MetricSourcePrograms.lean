import EvenProgram

/-! The two bare operator images use the same three coefficient
programs as the metric-derived source proofs. -/
namespace SchwarzschildMixtures.MetricSourcePrograms

open SchwarzschildEinstein.PureOdd ExactRational

local instance (n : Nat) : OfNat Formula n := ⟨.integer n⟩

def gammaFormula (ell : Formula) : Formula := (ell-1)*ell*(ell+1)*(ell+2)/12

def ratio (k ell : Formula) : Formula :=
  let g := gammaFormula ell
  let G := gammaFormula (2*ell)/2
  (G+g)*(g-k)/((G-g)*(g+k))

def first : Quadratic Formula :=
  plus Polar.coefficients (plus Mixed.coefficients PureOddProgram.coefficients)

def difference : Quadratic Formula :=
  plus Mixed.coefficients (scale (1+ratio .frequency .angular) PureOddProgram.coefficients)

unsafe def exportSources : IO Unit := do
  let (indices, operations) := Polar.exportFormulaList
    [first.1, first.2.1, first.2.2, difference.1, difference.2.1, difference.2.2]
  for row in operations do
    IO.println row
  IO.println ("outputs " ++ String.intercalate " " (indices.map toString))

end SchwarzschildMixtures.MetricSourcePrograms
