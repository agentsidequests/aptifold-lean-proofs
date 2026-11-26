import MixedAngularData

/-! The constant and linear Ricci coefficients in the same full-angle
coordinate calculation used for the quadratic source. -/
namespace SchwarzschildEinstein.PureOdd.Vacuum

open AngularArithmetic AngularCalculation

section Calculation
universe u
variable {S : Type u} [Zero S] [Add S] [Neg S] [Mul S]

def backgroundRicci (half : S) (g : SecondMetric S) (B : Axis → FirstJet S)
    (a b : Axis) : S :=
  let G₀ := christoffelDiag half B g
  divergence G₀ a b + product G₀ G₀ a b

def parentRicci (half : S) (g : SecondMetric S) (B : Axis → FirstJet S)
    (H : SecondMetric S) (a b : Axis) : S :=
  let G₀ := christoffelDiag half B g
  let h : FirstMetric S := fun i j => (H i j).toFirstJet
  let G₁ := connectionAdd (christoffelDiag half B H)
    (christoffel half (matNeg (inverseOne B h)) g)
  divergence G₁ a b + (product G₀ G₁ a b + product G₁ G₀ a b)

end Calculation

private def cosine := Fraction.indeterminate 1
private def metric := affineBackground cosine
private def inverse := affineInverse cosine (Fraction.inverse ⟨0, 0, 1⟩)

def backgroundAt (a b : Axis) : Fraction :=
  backgroundRicci (Fraction.constant (1/2)) metric inverse a b

def evenAt (a b : Axis) : Fraction :=
  parentRicci (Fraction.constant (1/2)) metric inverse (Mixed.polarParent cosine) a b

def oddAt (a b : Axis) : Fraction :=
  parentRicci (Fraction.constant (1/2)) metric inverse (affineParent cosine) a b

end SchwarzschildEinstein.PureOdd.Vacuum
