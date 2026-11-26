import PureOddCoordinates
import Mathlib.Tactic.FinCases

/-! Verify the jets of the Schwarzschild chart and rephased angular
columns used in the pure-odd calculation. The value of v in these jets
is one, and its polar derivative is one. -/
namespace SchwarzschildEinstein.PureOdd

open SecondJet

noncomputable section

variable {K : Type*} [Field K]

omit [Field K] in
theorem jet_ext {x y : SecondJet K} (val : x.value = y.value)
    (first : ∀ a, x.gradient a = y.gradient a)
    (second : ∀ a b, x.second a b = y.second a b) : x = y := by
  have d := funext first
  have d2 := funext fun a => funext (second a)
  cases x with
  | mk x₁ x₂ =>
    cases y with
    | mk y₁ y₂ =>
      cases x₁
      cases y₁
      cases val
      cases d
      cases d2
      rfl

omit [Field K] in
theorem first_jet_ext {x y : FirstJet K} (val : x.value = y.value)
    (first : ∀ a, x.gradient a = y.gradient a) : x = y := by
  have d := funext first
  cases x
  cases y
  cases val
  cases d
  rfl

theorem axis_constant (a : Axis) (x : K) : constant x = oneAxis a x 0 0 := by
  apply jet_ext
  · rfl
  · intro i
    simp [constant, FirstJet.constant, oneAxis]
  · intro i j
    simp [constant, oneAxis]

theorem axis_add (a : Axis) (x dx d2x y dy d2y : K) :
    add (oneAxis a x dx d2x) (oneAxis a y dy d2y) = oneAxis a (x+y) (dx+dy) (d2x+d2y) := by
  apply jet_ext
  · rfl
  · intro i
    by_cases hi : i = a <;> simp [add, FirstJet.add, oneAxis, hi]
  · intro i j
    by_cases hi : i = a <;> by_cases hj : j = a <;> simp [add, oneAxis, hi, hj]

theorem axis_neg (a : Axis) (x dx d2x : K) :
    neg (oneAxis a x dx d2x) = oneAxis a (-x) (-dx) (-d2x) := by
  apply jet_ext
  · rfl
  · intro i
    by_cases hi : i = a <;> simp [neg, FirstJet.neg, oneAxis, hi]
  · intro i j
    by_cases hi : i = a <;> by_cases hj : j = a <;> simp [neg, oneAxis, hi, hj]

theorem axis_mul (a : Axis) (x dx d2x y dy d2y : K) :
    mul (oneAxis a x dx d2x) (oneAxis a y dy d2y) =
      oneAxis a (x*y) (dx*y+x*dy) (d2x*y+dx*dy+dx*dy+x*d2y) := by
  apply jet_ext
  · rfl
  · intro i
    by_cases hi : i = a <;> simp [mul, FirstJet.mul, oneAxis, hi]
  · intro i j
    by_cases hi : i = a <;> by_cases hj : j = a <;> simp [mul, oneAxis, hi, hj]

theorem axis_inv (a : Axis) (x dx d2x : K) :
    inv (oneAxis a x dx d2x) =
      oneAxis a x⁻¹ (-dx/x^2) (2*dx*dx/x^3-d2x/x^2) := by
  apply jet_ext
  · rfl
  · intro i
    by_cases hi : i = a <;> simp [inv, oneAxis, hi]
  · intro i j
    by_cases hi : i = a <;> by_cases hj : j = a <;> simp [inv, oneAxis, hi, hj]

private def v : SecondJet K := polar 1 1 0
private def rr (r : K) : SecondJet K := oneAxis 1 r 1 0
private def angularDenominator : SecondJet K := add (constant 1) (mul (v : SecondJet K) v)

private def sphereV : SecondJet K :=
  divide (constant 4) (mul (angularDenominator : SecondJet K) angularDenominator)

private def sphereQ : SecondJet K := neg (mul (mul (v : SecondJet K) v) sphereV)

/-- The unit sphere metric jets. Two constant coordinate directions
let the angular calculations reuse the coordinate connection. -/
def sphereChartMetric (a b : Axis) : SecondJet K :=
  if a ≠ b then constant 0
  else if a = 2 then sphereV
  else if a = 3 then sphereQ
  else constant 1

variable [CharZero K]

theorem sphere_chart_jets :
    (sphereV : SecondJet K) = polar 1 (-2) 4 ∧
    (sphereQ : SecondJet K) = polar (-1) 0 2 := by
  constructor <;> norm_num [sphereQ, sphereV, angularDenominator, v, polar, divide,
    axis_constant 2, axis_add, axis_mul, axis_inv, axis_neg]

theorem odd_angular_jets (ell : K) :
    divide (constant ell) v = polar ell (-ell) (2*ell) ∧
      mul (constant ell) (divide (sub (constant 1) (mul v v)) angularDenominator) =
        polar 0 (-ell) ell := by
  constructor <;> norm_num [angularDenominator, v, polar, divide, sub,
    axis_constant 2, axis_add, axis_mul, axis_inv, axis_neg] <;> congr 1 <;> ring

private def modeBase : SecondJet K :=
  divide (mul (constant 2) v) angularDenominator

private theorem mode_base_jet : (modeBase : SecondJet K) = polar 1 0 (-1) := by
  norm_num [modeBase, angularDenominator, v, polar, divide, axis_constant 2,
    axis_add, axis_mul, axis_inv]

def jetPow (x : SecondJet K) : ℕ → SecondJet K
  | 0 => constant 1
  | n+1 => mul (jetPow x n) x

theorem equatorial_mode_power (n : ℕ) :
    (jetPow modeBase n : SecondJet K) = polar 1 0 (-(n:K)) := by
  induction n with
  | zero => simp [jetPow, polar, axis_constant 2]
  | succ n ih =>
    rw [jetPow, ih, mode_base_jet]
    simp [polar, axis_mul, Nat.cast_succ]
    congr 1
    ring

/-- The quadratic Taylor polynomial of the exponential with the phase
normalized to one at the evaluation point. -/
def exponentialJet (k ell : K) : SecondJet K :=
  let rate : Axis → K := fun i => if i = 0 then -k else if i = 3 then ell else 0
  let z : SecondJet K := ⟨⟨0, rate⟩, fun _ _ => 0⟩
  add (constant 1) (add z (mul (constant (1/2)) (mul z z)))

theorem exponential_phase_jet (k ell : K) :
    let rate : Axis → K := fun i => if i = 0 then -k else if i = 3 then ell else 0
    exponentialJet k ell = ⟨⟨1, rate⟩, fun i j => rate i*rate j⟩ := by
  dsimp only
  apply jet_ext
  · simp [exponentialJet, add, FirstJet.add, mul, FirstJet.mul, constant, FirstJet.constant]
  · intro i
    simp [exponentialJet, add, FirstJet.add, mul, FirstJet.mul, constant, FirstJet.constant]
  · intro i j
    simp only [exponentialJet, add, FirstJet.add, mul, FirstJet.mul, constant, FirstJet.constant,
      zero_mul, mul_zero, add_zero, zero_add, mul_one, one_mul]
    ring

theorem carrier_from_mode (k : K) (n : ℕ) :
    mul (exponentialJet k (n:K)) (jetPow modeBase n) = carrier k (n:K) := by
  rw [equatorial_mode_power, exponential_phase_jet]
  apply jet_ext
  · simp [mul, FirstJet.mul, polar, oneAxis, carrier]
  · intro i
    simp [mul, FirstJet.mul, polar, oneAxis, carrier]
  · intro i j
    by_cases hi : i = 2 <;> by_cases hj : j = 2 <;>
      simp [mul, FirstJet.mul, polar, oneAxis, carrier, hi, hj]

/-- The squared parent carrier has the doubled frequency and angular
label of the daughter. This identity includes all second derivatives. -/
theorem daughter_carrier_from_parent (k ell : K) :
    mul (carrier k ell) (carrier k ell) = carrier (2*k) (2*ell) := by
  apply jet_ext
  · norm_num [mul, FirstJet.mul, carrier]
  · intro i
    fin_cases i <;> norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, mul, FirstJet.mul, carrier] <;> ring
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, mul, FirstJet.mul, carrier] <;> ring

omit [CharZero K] in
private theorem radial_lapse_jet (r : K) (hr : r ≠ 0) :
    divide (sub (rr r) (constant 2)) (rr r) =
      oneAxis 1 ((r-2)/r) (2/r^2) (-(4/r^3)) := by
  norm_num [rr, divide, sub, axis_constant 1, axis_add, axis_mul, axis_inv, axis_neg]
  congr 1 <;> field_simp [hr] <;> ring

omit [CharZero K] in
private theorem radial_square_jet (r : K) :
    mul (rr r) (rr r) = oneAxis 1 (r^2) (2*r) 2 := by
  rw [rr, axis_mul]
  congr 1 <;> ring

theorem schwarzschild_background_jets (r : K) (hr : r ≠ 0) (hh : r-2 ≠ 0) :
    let rad := rr r
    let f := divide (sub rad (constant 2)) rad
    let g := background r
    g 0 0 = neg f ∧ g 1 1 = inv f ∧
      g 2 2 = mul (mul rad rad) sphereV ∧ g 3 3 = mul (mul rad rad) sphereQ ∧
      (∀ i j, i ≠ j → g i j = constant 0) := by
  obtain ⟨hv, hq⟩ := sphere_chart_jets (K := K)
  dsimp only
  rw [hv, hq, radial_lapse_jet r hr, radial_square_jet r]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, background, axis_neg, neg_div]
    congr 1
    ring
  · norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, background, axis_inv]
    congr 1 <;> field_simp [hr, hh] <;> ring
  · norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, background]
  · norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, background]
  · intro i j hij
    simp [background, hij]

/-- The inverse used in the Ricci calculation has the value and all
four first derivatives of the reciprocal diagonal metric. -/
theorem schwarzschild_inverse_jets (r : K) (hr : r ≠ 0) (hh : r-2 ≠ 0) :
    backgroundInverse r = jetDiagonal (fun a => (inv (background r a a)).toFirstJet) := by
  have reverse_horizon : 2-r ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hh))
  unfold backgroundInverse
  congr 1
  funext a
  fin_cases a <;> apply first_jet_ext
  all_goals try (intro i; fin_cases i)
  all_goals
    norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff, inverseDiagonal, background, inv,
      mul, FirstJet.mul, oneAxis, polar] <;> field_simp [hr, hh, reverse_horizon] <;> ring

omit [CharZero K] in
private theorem derivative_of_power_at_rate [Algebra ℚ K] (d : Derivation ℚ K K)
    (x rate : K) (growth : d x = rate*x) (n : ℕ) :
    d (x^n) = (n:K)*rate*x^n := by
  induction n with
  | zero => simp [d.map_one_eq_zero]
  | succ n ih =>
    rw [pow_succ, d.leibniz, ih, growth, Nat.cast_succ]
    simp only [smul_eq_mul]
    ring

/-- Derive the rephased axial covector from the highest-weight mode
before evaluating at the equator. In this chart its entries are
`∂q Y / v` and `v ∂v Y`. -/
theorem axial_covector_from_mode [Algebra ℚ K] (dv dq : Derivation ℚ K K)
    (x phase : K) (n : ℕ) (hx : x ≠ 0) (hd : 1+x^2 ≠ 0)
    (vx : dv x = 1) (qx : dq x = 0) (vp : dv phase = 0)
    (qp : dq phase = (n:K)*phase) :
    let Y := phase*(2*x/(1+x^2))^n
    dq Y/x = ((n:K)/x)*Y ∧ x*dv Y = (n:K)*((1-x^2)/(1+x^2))*Y := by
  let base : K := 2*x/(1+x^2)
  have dv_two : dv (2 : K) = 0 := by simpa using dv.map_natCast 2
  have dq_two : dq (2 : K) = 0 := by simpa using dq.map_natCast 2
  have dv_num : dv (2*x) = 2 := by
    rw [dv.leibniz, dv_two, vx]
    simp [smul_eq_mul]
  have dv_den : dv (1+x^2) = 2*x := by
    simp only [map_add, dv.map_one_eq_zero, zero_add, pow_two, dv.leibniz, vx, smul_eq_mul, mul_one]
    ring
  have dv_base : dv base = ((1-x^2)/(x*(1+x^2)))*base := by
    dsimp only [base]
    rw [dv.leibniz_div, dv_num, dv_den]
    simp only [smul_eq_mul]
    field_simp [hx, hd]
    ring
  have dq_base : dq base = 0 := by
    simp [base, dq.leibniz_div, pow_two, dq.leibniz, qx, dq_two, dq.map_one_eq_zero, smul_eq_mul]
  have dv_power := derivative_of_power_at_rate dv base _ dv_base n
  have dq_power : dq (base^n) = 0 := by simp only [dq.leibniz_pow, dq_base, smul_zero]
  change dq (phase*base^n)/x = ((n:K)/x)*(phase*base^n) ∧
    x*dv (phase*base^n) = (n:K)*((1-x^2)/(1+x^2))*(phase*base^n)
  constructor
  · rw [dq.leibniz, dq_power, qp]
    simp only [smul_eq_mul, mul_zero, zero_add, div_eq_mul_inv]
    ring
  · rw [dv.leibniz, dv_power, vp]
    simp only [smul_eq_mul, mul_zero, add_zero]
    field_simp [hx, hd]

/-- Substitute the angular mode and both rephased covector components
into every entry of the odd Regge–Wheeler-gauge parent. -/
theorem parent_metric_from_mode (k : K) (n : ℕ) (T P : RadialJet K) :
    let ell : K := n
    let mode := mul (exponentialJet k ell) (jetPow modeBase n)
    let Xv := mul mode (divide (constant ell) v)
    let Xq := mul mode (mul (constant ell) (divide (sub (constant 1) (mul v v)) angularDenominator))
    parentMetric k ell T P = fun i j =>
      if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then neg (mul (radial T) Xv)
      else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then neg (mul (radial T) Xq)
      else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then neg (mul (radial P) Xv)
      else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then neg (mul (radial P) Xq)
      else constant 0 := by
  obtain ⟨hv, hq⟩ := odd_angular_jets (n : K)
  dsimp only
  rw [carrier_from_mode, hv, hq]
  rfl

#print axioms sphere_chart_jets
#print axioms odd_angular_jets
#print axioms carrier_from_mode
#print axioms daughter_carrier_from_parent
#print axioms schwarzschild_background_jets
#print axioms schwarzschild_inverse_jets
#print axioms axial_covector_from_mode
#print axioms parent_metric_from_mode

end
end SchwarzschildEinstein.PureOdd
