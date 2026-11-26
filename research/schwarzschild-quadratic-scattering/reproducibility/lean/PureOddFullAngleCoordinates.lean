import PureOddCoordinates
import Mathlib.Tactic.FinCases

/-! Full-angle jets in a locally scaled stereographic coordinate.
At the point v₀ the polar derivative is v₀ times the v derivative and
the second derivative is v₀² times the v Hessian. The scale v₀ is held
constant when differentiating. The common parent carrier is divided
by its value at the point. -/
namespace SchwarzschildEinstein.PureOdd

open SecondJet

noncomputable section

variable {K : Type*} [Field K]

/-- With c = cos θ, the squared sine controls the angular metric. -/
def sineSquared (c : K) : K := 1-c^2

def fullAngleBackground (r c : K) : SecondMetric K :=
  let s := sineSquared c
  let radius := oneAxis 1 (r^2) (2*r) 2
  fun a b =>
    if a ≠ b then constant 0
    else if a = 0 then background r 0 0
    else if a = 1 then background r 1 1
    else if a = 2 then mul radius (polar s (2*(c-1)*s) ((4*c^2-10*c+6-2*s)*s))
    else mul radius (polar (-s) (-(2*c*s)) (-(2*(2*c^2-c-s)*s)))

def fullAngleInverseDiagonal (r c : K) (a : Axis) : FirstJet K :=
  let s := sineSquared c
  let radius := oneAxis 1 (1/r^2) (-(2/r^3) : K) (6/r^4)
  if a = 0 ∨ a = 1 then inverseDiagonal r a
  else if a = 2 then (mul radius (polar (1/s) (-(2*(c-1)/s)) 0)).toFirstJet
  else (mul radius (polar (-(1/s)) (2*c/s) 0)).toFirstJet

def fullAngleBackgroundInverse (r c : K) : FirstMetric K :=
  jetDiagonal (fullAngleInverseDiagonal r c)

def fullAngleCarrier (k ell c : K) : SecondJet K :=
  let rate : Axis → K := fun a =>
    if a = 0 then -k else if a = 3 then ell else if a = 2 then ell*c else 0
  ⟨⟨1, rate⟩, fun a b => rate a*rate b -
    (if a = 2 ∧ b = 2 then ell*(sineSquared c+c) else 0)⟩

def fullAngleParentMetric (k ell c : K) (T P : RadialJet K) : SecondMetric K :=
  let s := sineSquared c
  let Y := fullAngleCarrier k ell c
  let vColumn := mul Y (polar ell (-ell) (2*ell))
  let qColumn := mul Y (polar (ell*c) (-(ell*s)) (ell*(1-2*c)*s))
  fun a b =>
    if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then neg (mul (radial T) vColumn)
    else if (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) then neg (mul (radial T) qColumn)
    else if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then neg (mul (radial P) vColumn)
    else if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then neg (mul (radial P) qColumn)
    else constant 0

def fullAngleRicci (r k ell c : K) (T P : RadialJet K) : Tensor Axis K :=
  quadraticJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c)
    (fullAngleParentMetric k ell c T P)

def fullAngleTensor (r k ell c : K) (T P : RadialJet K) : Tensor Axis K :=
  -(einstein (1/2) (fun a b => (fullAngleBackground r c a b).value)
    (fun a b => (fullAngleBackgroundInverse r c a b).value) (fullAngleRicci r k ell c T P))

variable [CharZero K]

omit [CharZero K] in
private theorem background_at_equator (r : K) :
    fullAngleBackground r 0 = background r := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, fullAngleBackground, background, sineSquared]

private theorem inverse_at_equator (r : K) :
    fullAngleBackgroundInverse r 0 = backgroundInverse r := by
  unfold fullAngleBackgroundInverse backgroundInverse
  congr 1
  funext a
  fin_cases a <;>
    norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, fullAngleInverseDiagonal, inverseDiagonal,
      sineSquared, polar, oneAxis, SecondJet.mul, FirstJet.mul]

private theorem carrier_at_equator (k ell : K) : fullAngleCarrier k ell 0 = carrier k ell := by
  simp [fullAngleCarrier, carrier, sineSquared]

private theorem parent_at_equator (k ell : K) (T P : RadialJet K) :
    fullAngleParentMetric k ell 0 T P = parentMetric k ell T P := by
  simpa [fullAngleParentMetric, parentMetric, carrier_at_equator, sineSquared] using
    (rfl : parentMetric k ell T P = parentMetric k ell T P)

theorem full_angle_ricci_at_equator (r k ell : K) (T P : RadialJet K) :
    fullAngleRicci r k ell 0 T P =
      quadraticJetRicci (background r) (backgroundInverse r) (parentMetric k ell T P) := by
  simp only [fullAngleRicci, background_at_equator, inverse_at_equator, parent_at_equator]

theorem full_angle_tensor_at_equator (r k ell : K) (T P : RadialJet K) :
    fullAngleTensor r k ell 0 T P = tensor r k ell T P := by
  simp only [fullAngleTensor, full_angle_ricci_at_equator, background_at_equator, inverse_at_equator, tensor]

#print axioms full_angle_ricci_at_equator
#print axioms full_angle_tensor_at_equator

end
end SchwarzschildEinstein.PureOdd
