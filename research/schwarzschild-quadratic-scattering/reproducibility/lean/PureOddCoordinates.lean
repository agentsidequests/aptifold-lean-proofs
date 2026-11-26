import CoordinateJets
import PureOddFormulas

/-! Pure odd Regge–Wheeler-gauge parent in the complex stereographic
chart. Coordinates are ordered t, r, v, q with q = i φ. All chart
derivatives are taken before setting v = 1. -/
namespace SchwarzschildEinstein.PureOdd

open scoped BigOperators
open SecondJet

noncomputable section

variable {K : Type*} [Field K]

def oneAxis (a : Axis) (x dx d2x : K) : SecondJet K :=
  ⟨⟨x, fun i => if i = a then dx else 0⟩,
    fun i j => if i = a ∧ j = a then d2x else 0⟩

def radial (a : RadialJet K) : SecondJet K := oneAxis 1 a.val a.first a.second
def polar (x dx d2x : K) : SecondJet K := oneAxis 2 x dx d2x

/-- The jet of the normalized factor
\((2v/(1+v^2))^\ell \exp(\ell q-kt)\) at the equator. -/
def carrier (k ell : K) : SecondJet K :=
  let rate : Axis → K := fun i => if i = 0 then -k else if i = 3 then ell else 0
  ⟨⟨1, rate⟩, fun i j => rate i*rate j - (if i = 2 ∧ j = 2 then ell else 0)⟩

def background (r : K) : SecondMetric K :=
  fun i j =>
    if i ≠ j then constant 0
    else if i = 0 then oneAxis 1 (-(r-2)/r) (-(2/r^2)) (4/r^3)
    else if i = 1 then oneAxis 1 (r/(r-2)) (-(2/(r-2)^2)) (4/(r-2)^3)
    else if i = 2 then mul (oneAxis 1 (r^2) (2*r) 2) (polar 1 (-2) 4)
    else mul (oneAxis 1 (r^2) (2*r) 2) (polar (-1) 0 2)

def inverseDiagonal (r : K) (i : Axis) : FirstJet K :=
    if i = 0 then (oneAxis 1 (-(r/(r-2))) (2/(r-2)^2 : K) (-(4/(r-2)^3))).toFirstJet
    else if i = 1 then (oneAxis 1 ((r-2)/r) (2/r^2 : K) (-(4/r^3))).toFirstJet
    else if i = 2 then (mul (oneAxis 1 (1/r^2) (-(2/r^3)) (6/r^4)) (polar 1 2 4)).toFirstJet
    else (mul (oneAxis 1 (1/r^2) (-(2/r^3)) (6/r^4)) (polar (-1) 0 (-2))).toFirstJet

def backgroundInverse (r : K) : FirstMetric K := jetDiagonal (inverseDiagonal r)

/-- The only nonzero parent components are mixed base-sphere entries.
They are minus the axial amplitudes times the rephased axial harmonics. -/
def parentMetric (k ell : K) (T P : RadialJet K) : SecondMetric K :=
  let vColumn := mul (carrier k ell) (polar ell (-ell) (2*ell))
  let qColumn := mul (carrier k ell) (polar 0 (-ell) ell)
  fun i j =>
    if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then neg (mul (radial T) vColumn)
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then neg (mul (radial T) qColumn)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then neg (mul (radial P) vColumn)
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then neg (mul (radial P) qColumn)
    else constant 0

def tensor (r k ell : K) (T P : RadialJet K) : Tensor Axis K :=
  let g := background r
  let B := backgroundInverse r
  let R := quadraticJetRicci g B (parentMetric k ell T P)
  show Tensor Axis K from
    -(einstein (1/2) (fun a b => (g a b).value) (fun a b => (B a b).value) R)

def projected (r k ell : K) (T P : RadialJet K) : EvenSource K :=
  let S := tensor r k ell T P
  let L := 2*ell
  ⟨S 0 0, S 1 1, S 1 3/L, (S 2 2-S 3 3)/2, (S 2 2+S 3 3)/(L*(L-1))⟩

end
end SchwarzschildEinstein.PureOdd
