import LinearLowFrequencyBarrier
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The regular static spin-two wave as a polynomial with positive
coefficients in the shifted radial variable. -/
namespace SchwarzschildLaurent.LinearWave

open Polynomial Finset

noncomputable section

def staticCoefficient (ell : ℕ) : ℕ → ℝ
  | 0 => 1/8
  | m+1 => (((ell:ℝ)*(ell+1)-((m:ℝ)+2)*((m:ℝ)+3))/(2*((m:ℝ)+1)^2))*
    staticCoefficient ell m

def staticEnvelope (ell : ℕ) : ℝ[X] :=
  ∑ m ∈ range (ell-1), monomial m (staticCoefficient ell m)

private theorem static_coefficient_recurrence (ell m : ℕ) :
    2*((m:ℝ)+1)^2*staticCoefficient ell (m+1) =
      ((ell:ℝ)*(ell+1)-((m:ℝ)+2)*((m:ℝ)+3))*staticCoefficient ell m := by
  simp only [staticCoefficient]
  have positive : 0 < ((m:ℝ)+1) := by positivity
  field_simp [positive.ne']

theorem static_coefficient_positive (ell : ℕ) (hell : 2 ≤ ell) (m : ℕ) (hm : m ≤ ell-2) :
    0 < staticCoefficient ell m := by
  induction m with
  | zero => norm_num [staticCoefficient]
  | succ m ih =>
    have first : (m:ℝ)+2 < (ell:ℝ) := by exact_mod_cast (show m+2 < ell by omega)
    have second : (m:ℝ)+3 ≤ (ell:ℝ)+1 := by exact_mod_cast (show m+3 ≤ ell+1 by omega)
    have left := mul_lt_mul_of_pos_right first (show 0 < (m:ℝ)+3 by positivity)
    have right := mul_le_mul_of_nonneg_left second (show 0 ≤ (ell:ℝ) by positivity)
    have gap := sub_pos.mpr (left.trans_le right)
    rw [staticCoefficient]
    exact mul_pos (div_pos gap (by positivity)) (ih (by omega))

theorem static_coefficient_stops (ell : ℕ) (hell : 2 ≤ ell) {m : ℕ} (hm : ell-1 ≤ m) :
    staticCoefficient ell m = 0 := by
  have stop : staticCoefficient ell (ell-1) = 0 := by
    have eq : ell-1 = (ell-2)+1 := by omega
    have shift : ((ell-2:ℕ):ℝ)+2 = (ell:ℝ) := by exact_mod_cast (show ell-2+2=ell by omega)
    have gap : (ell:ℝ)*(ell+1)-(((ell-2:ℕ):ℝ)+2)*(((ell-2:ℕ):ℝ)+3) = 0 := by
      rw [← shift]
      ring
    rw [eq,staticCoefficient,gap,zero_div,zero_mul]
  induction hm with
  | refl => exact stop
  | step _ i => rw [staticCoefficient,i,mul_zero]

theorem static_envelope_coeff (ell : ℕ) (hell : 2 ≤ ell) (m : ℕ) :
    (staticEnvelope ell).coeff m = staticCoefficient ell m := by
  classical
  by_cases hm : m < ell-1
  · simp [staticEnvelope,coeff_monomial,hm]
  · simp [staticEnvelope,coeff_monomial,hm,
      static_coefficient_stops ell hell (Nat.le_of_not_gt hm)]

private def euler (P : ℝ[X]) : ℝ[X] := X*P.derivative

private theorem euler_coeff (P : ℝ[X]) (m : ℕ) : (euler P).coeff m = (m:ℝ)*P.coeff m := by
  cases m with
  | zero => simp [euler]
  | succ m =>
    rw [euler,coeff_X_mul,coeff_derivative,Nat.cast_add,Nat.cast_one]
    ring

/-- The polynomial differential equation in the variable `s = r-2`. -/
theorem static_envelope_equation (ell : ℕ) (hell : 2 ≤ ell) :
    let P := staticEnvelope ell
    (X^2+C 2*X)*P.derivative.derivative+
      (C 6*X+C 2)*P.derivative+C (6-(ell:ℝ)*(ell+1))*P = 0 := by
  let P := staticEnvelope ell
  have exact_coefficients :
      euler (euler P)+C 5*euler P+C 2*(euler P).derivative+C (6-(ell:ℝ)*(ell+1))*P = 0 := by
    ext m
    simp only [coeff_add,coeff_C_mul,euler_coeff,coeff_derivative,P,static_envelope_coeff ell hell,
      coeff_zero,Nat.cast_succ]
    linear_combination static_coefficient_recurrence ell m
  calc
    _ = euler (euler P)+C 5*euler P+C 2*(euler P).derivative+C (6-(ell:ℝ)*(ell+1))*P := by
      simp only [euler,derivative_mul,derivative_X,one_mul,map_ofNat]
      ring
    _ = _ := exact_coefficients

theorem static_envelope_leading_lower (ell : ℕ) (hell : 2 ≤ ell) (s : ℝ) (hs : 0 ≤ s) :
    staticCoefficient ell (ell-2)*s^(ell-2) ≤ (staticEnvelope ell).eval s := by
  have last : ell-2 ∈ range (ell-1) := mem_range.2 (by omega)
  simp only [staticEnvelope,eval_finsetSum,eval_monomial]
  exact single_le_sum (fun m hm => mul_nonneg
    (static_coefficient_positive ell hell m (by have h := mem_range.mp hm; omega)).le (pow_nonneg hs m)) last

def staticWave (ell : ℕ) (r : ℝ) : ℝ := r^3*(staticEnvelope ell).eval (r-2)

theorem static_wave_growth (ell : ℕ) (hell : 2 ≤ ell) {r : ℝ} (hr : 4 ≤ r) :
    (staticCoefficient ell (ell-2)/2^(ell-2))*r^(ell+1) ≤ staticWave ell r := by
  have start : 0 ≤ r/2 := by linarith
  have shifted : r/2 ≤ r-2 := by linarith
  have m := pow_le_pow_left₀ start shifted (ell-2)
  have coeff := (static_coefficient_positive ell hell (ell-2) le_rfl).le
  have exponent : ell+1 = 3+(ell-2) := by omega
  calc
    _ = r^3*(staticCoefficient ell (ell-2)*(r/2)^(ell-2)) := by rw [exponent,pow_add,div_pow]; ring
    _ ≤ r^3*(staticCoefficient ell (ell-2)*(r-2)^(ell-2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m coeff) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (static_envelope_leading_lower ell hell _ (by linarith)) (by positivity)

def staticWaveJet (ell : ℕ) (r : ℝ) : ℝ :=
  realLapse r*(3*(r^2*(staticEnvelope ell).eval (r-2))+r^3*(staticEnvelope ell).derivative.eval (r-2))

/-- Restore the areal-radius value and the tortoise derivative of the
static polynomial and check the actual radial system. -/
theorem static_wave_radial_equation (ell : ℕ) (hell : 2 ≤ ell) {r : ℝ} (hr : 2 < r) :
    HasDerivAt (staticWave ell) (staticWaveJet ell r/realLapse r) r ∧
    HasDerivAt (staticWaveJet ell) (realBarrier ell 0 r*staticWave ell r/realLapse r) r := by
  let P := staticEnvelope ell
  let p := fun s : ℝ => P.eval (s-2)
  let dp := fun s : ℝ => P.derivative.eval (s-2)
  let ddp := fun s : ℝ => P.derivative.derivative.eval (s-2)
  have d₀ : HasDerivAt p (dp r) r := by
    simpa only [p,dp,Function.comp_def,id_eq,mul_one] using
      (P.hasDerivAt (r-2)).comp r ((hasDerivAt_id r).sub_const 2)
  have d₁ : HasDerivAt dp (ddp r) r := by
    simpa only [dp,ddp,Function.comp_def,id_eq,mul_one] using
      (P.derivative.hasDerivAt (r-2)).comp r ((hasDerivAt_id r).sub_const 2)
  have r0 : r ≠ 0 := by linarith
  have f0 : realLapse r ≠ 0 := div_ne_zero (sub_ne_zero.mpr hr.ne') r0
  have fDeriv : HasDerivAt realLapse (2/r^2) r := by
    apply (((hasDerivAt_id r).sub_const 2).div (hasDerivAt_id r) r0).congr_deriv
    dsimp only [id_eq]
    ring
  have ode₀ := congrArg (fun F : ℝ[X] => F.eval (r-2)) (static_envelope_equation ell hell)
  simp only [eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_zero] at ode₀
  have ode : r*(r-2)*ddp r+(6*r-10)*dp r+(6-(ell:ℝ)*(ell+1))*p r = 0 := by
    dsimp only [p,dp,ddp,P]
    linear_combination ode₀
  have dR2 : HasDerivAt (fun s : ℝ => s^2) (2*r) r := by
    change HasDerivAt (id ^ 2) (2*r) r
    simpa only [Nat.cast_ofNat,id_eq,Nat.reduceSub,pow_one,mul_one] using (hasDerivAt_id r).pow 2
  have dR3 : HasDerivAt (fun s : ℝ => s^3) (3*r^2) r := by
    change HasDerivAt (id ^ 3) (3*r^2) r
    simpa only [Nat.cast_ofNat,id_eq,Nat.reduceSub,mul_one] using (hasDerivAt_id r).pow 3
  constructor
  · apply (dR3.mul d₀).congr_deriv
    unfold staticWaveJet
    rw [mul_div_cancel_left₀ _ f0]
    dsimp only [p,dp,P]
    ring
  · apply (fDeriv.mul (((dR2.mul d₀).const_mul 3).add (dR3.mul d₁))).congr_deriv
    have target : realBarrier ell 0 r*staticWave ell r/realLapse r =
        ((ell:ℝ)*(ell+1)/r^2-6/r^3)*(r^3*p r) := by
      simp only [realBarrier,staticWave,p,P,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero]
      field_simp [f0]
    rw [target]
    dsimp only [Pi.mul_apply,Pi.add_apply]
    calc
      _ = ((ell:ℝ)*(ell+1)/r^2-6/r^3)*(r^3*p r) +
          r*(r*(r-2)*ddp r+(6*r-10)*dp r+(6-(ell:ℝ)*(ell+1))*p r) := by
        unfold realLapse
        field_simp [r0]
        ring
      _ = _ := by rw [ode,mul_zero,add_zero]

#print axioms static_coefficient_positive
#print axioms static_coefficient_stops
#print axioms static_envelope_coeff
#print axioms static_envelope_equation
#print axioms static_envelope_leading_lower
#print axioms static_wave_growth
#print axioms static_wave_radial_equation

end
end SchwarzschildLaurent.LinearWave
