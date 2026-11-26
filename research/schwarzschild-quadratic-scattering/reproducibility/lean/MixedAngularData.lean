import PureOddAngularData

/-! Exact computation of the part of the daughter vector quadratic in
one polar and one axial parent. The polar sphere amplitude includes
the factor r². The axial amplitudes use the same normalization as
PureOddAngularData. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open AngularArithmetic AngularCalculation

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

def polarParent (c : Fraction) : SecondMetric Fraction :=
  let Y := affineCarrier c
  let s := sin2 c
  let vv := axisJet 2 s (Q 2*(c + -(Q 1))*s)
    ((Q 4*c*c + -(Q 10*c) + Q 6 + -(Q 2*s))*s)
  let qq := axisJet 2 (-s) (-(Q 2*c*s)) (-(Q 2*(Q 2*c*c + -c + -s)*s))
  let radial (i : Nat) := axisJet 1 (X i) (X (i+1)) (X (i+2))
  fun a b =>
    if a = 0 ∧ b = 0 then secondMul (radial 10) Y
    else if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then secondMul (radial 13) Y
    else if a = 1 ∧ b = 1 then secondMul (radial 16) Y
    else if a = 2 ∧ b = 2 then secondMul (radial 19) (secondMul Y vv)
    else if a = 3 ∧ b = 3 then secondMul (radial 19) (secondMul Y qq)
    else axisJet 2 0 0 0

def addJets {S : Type} [Add S] (x y : SecondJet S) : SecondJet S :=
  ⟨firstAdd x.toFirstJet y.toFirstJet, fun i j => x.second i j+y.second i j⟩

def mixedParts (c u : Fraction) (a b : Axis) : Axis → Fraction :=
  let g := affineBackground c
  let B := affineInverse c u
  let E := polarParent c
  let O := affineParent c
  let contributions := ricciParts (Q (1/2)) g B
  fun i => contributions (fun x y => addJets (E x y) (O x y)) a b i +
    -(contributions E a b i) + -(contributions O a b i)

def mixedRicci (c u : Fraction) (a b : Axis) : Fraction :=
  let s := mixedParts c u a b
  s 0 + (s 1 + s 2 + s 3)

theorem combineParts (c u : Fraction) (a b : Axis) (w x y z : Fraction)
    (h₀ : mixedParts c u a b 0 = w) (h₁ : mixedParts c u a b 1 = x)
    (h₂ : mixedParts c u a b 2 = y) (h₃ : mixedParts c u a b 3 = z) :
    mixedRicci c u a b = w+(x+y+z) := by
  unfold mixedRicci
  dsimp only
  rw [h₀,h₁,h₂,h₃]

def atAngle (a b : Axis) : Fraction :=
  mixedRicci (X 1) (Fraction.inverse ⟨0,0,1⟩) a b

def atEquator (a b : Axis) : Fraction := mixedRicci (Q 0) (Q 1) a b

end SchwarzschildEinstein.PureOdd.Mixed
