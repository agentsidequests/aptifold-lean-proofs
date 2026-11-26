import MixedAngularFormulaData

/-! The equatorial angular coefficient of the mixed Ricci tensor, with the
common daughter carrier factored out. The polar sphere amplitude U includes
the background factor r², as in the coordinate parent metric. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open AngularArithmetic

def angularRicciCoefficient {K : Type u} [Add K] [Neg K] [Mul K]
    (C : Rat → K) (r invR f invF k ell : K) (T P : RadialJet K)
    (E : PolarParentJets K) : K :=
  let A := E.tt
  let B := E.tr
  let H := E.rr
  let U := E.sphere
  let invR2 := invR*invR
  let f2 := f*f
  let radial :=
    -(C (3/4)*k*invF*invF*T.val*A.val)
      + -(C (1/4)*k*T.val*H.val)
      + k*P.val*B.val
      + -(C (1/2)*(T.val*B.first+T.first*B.val))
      + C (1/4)*P.val*(A.first+f2*H.first)
      + C (1/2)*f2*P.first*H.val
      + -(C (1/2)*invF*invR2*P.val*A.val)
      + C (3/2)*f*invR2*P.val*H.val
  let sphere :=
    k*invF*invR2*T.val*U.val
      + C (1/2)*f*invR2*(P.val*U.first+P.first*U.val)
      + -((r+ -(C 3))*invR2*invR2*P.val*U.val)
  ell*(ell+ -(C 1))*radial+ell*ell*sphere

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

def symbolicAngularRicci : Fraction :=
  let r := X 0
  angularRicciCoefficient Q r (rInv 1) ((r+ -(Q 2))*rInv 1) (r*hInv 1) (X 2) (X 3)
    (radialSymbols 4) (radialSymbols 7)
    ⟨radialSymbols 10, radialSymbols 13, radialSymbols 16, radialSymbols 19⟩

def predictedTensor (a b : Axis) : Fraction :=
  if a.val < 2 ∧ b.val < 2 then 0
  else if a.val < 2 then predictedVector a b
  else if b.val < 2 then predictedVector b a
  else (if a = b then Q 2*X 1 else Q 1+X 1*X 1)*symbolicAngularRicci

end SchwarzschildEinstein.PureOdd.Mixed
