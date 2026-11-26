import MixedAngularData
import MixedVectorFormulas

namespace SchwarzschildEinstein.PureOdd.Mixed

open AngularArithmetic

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

def radialSymbols (i : Nat) : RadialJet Fraction := ⟨X i, X (i+1), X (i+2)⟩

def symbolicVector : AxialVector Fraction :=
  let r := X 0
  let h := r + -(Q 2)
  vectorCoefficients Q r (rInv 1) (h*rInv 1) (r*hInv 1) (X 2) (X 3)
    (radialSymbols 4) (radialSymbols 7)
    ⟨radialSymbols 10, radialSymbols 13, radialSymbols 16, radialSymbols 19⟩

def predictedPolar (a : Axis) : Fraction :=
  (Q 2*X 3) * (if a = 0 then symbolicVector.time else symbolicVector.radius)

def predictedVector (a b : Axis) : Fraction :=
  if b = 2 then predictedPolar a else X 1 * predictedPolar a

end SchwarzschildEinstein.PureOdd.Mixed
