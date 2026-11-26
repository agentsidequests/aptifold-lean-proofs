import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! Consequences of a logarithmic relative phase for the light-ring
strain. The asymptotic input is supplied by the radial matching argument. -/
namespace SchwarzschildMixtures.Strain.LightRing

open Filter
open scoped Topology

noncomputable section

def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ)*Complex.I)

private theorem phase_continuous : Continuous phase :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

private theorem phase_periods (t : ℝ) (n : ℕ) : phase (t+2*Real.pi*n) = phase t := by
  have turn : (((2*Real.pi*(n : ℝ) : ℝ) : ℂ)*Complex.I) =
      (n : ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add, turn,
    Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

/-- The integer degrees return arbitrarily close to any prescribed
    relative phase. No continuum approximation in the angular label is needed. -/
theorem logarithmic_phase_subsequence (start target : ℝ) :
    ∃ degrees : ℕ → ℕ, Tendsto degrees atTop atTop ∧
      Tendsto (fun j => phase (Real.log (degrees j : ℝ)/2+start)) atTop (𝓝 (phase target)) := by
  let exponent : ℕ → ℝ := fun j => 2*(target-start)+(4*Real.pi)*j
  have linear : Tendsto exponent atTop atTop :=
    tendsto_atTop_add_const_left atTop _ ((tendsto_natCast_atTop_atTop : Tendsto
      (fun j : ℕ => (j : ℝ)) atTop atTop).const_mul_atTop (by positivity : 0 < 4*Real.pi))
  let size : ℕ → ℝ := fun j => Real.exp (exponent j)
  have large : Tendsto size atTop atTop := Real.tendsto_exp_atTop.comp linear
  let degree : ℕ → ℕ := fun j => ⌊size j⌋₊
  have tends : Tendsto degree atTop atTop := tendsto_nat_floor_atTop.comp large
  have quotient : Tendsto (fun j => (degree j : ℝ)/size j) atTop (𝓝 1) := by
    have floorRatio : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)/x) atTop (𝓝 1) := by
      simpa only [one_mul] using tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := 1) zero_le_one
    exact floorRatio.comp large
  have ratioLog := (Real.continuousAt_log one_ne_zero).tendsto.comp quotient
  rw [Real.log_one] at ratioLog
  have diff : Tendsto (fun j => Real.log (degree j : ℝ)-exponent j) atTop (𝓝 0) := by
    apply ratioLog.congr'
    filter_upwards [tendsto_atTop.mp tends 1] with j hj
    have pos : 0 < (degree j : ℝ) := by exact_mod_cast (show 0 < degree j by omega)
    change Real.log ((degree j : ℝ)/Real.exp (exponent j)) = _
    rw [Real.log_div pos.ne' (Real.exp_ne_zero _), Real.log_exp]
  refine ⟨degree,tends,?_⟩
  have corrected : Tendsto (fun j => phase (target+(Real.log (degree j : ℝ)-exponent j)/2))
      atTop (𝓝 (phase target)) := by
    apply phase_continuous.continuousAt.tendsto.comp
    simpa only [zero_div, add_zero] using tendsto_const_nhds.add (diff.div_const 2)
  apply corrected.congr
  intro j
  rw [show Real.log (degree j : ℝ)/2+start =
      (target+(Real.log (degree j : ℝ)-exponent j)/2)+2*Real.pi*j by dsimp [exponent]; ring]
  rw [phase_periods]

theorem two_term_magnitude_bounds (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a-b| ≤ ‖(a : ℂ)+(b : ℂ)*phase t‖ ∧ ‖(a : ℂ)+(b : ℂ)*phase t‖ ≤ a+b := by
  have anorm : ‖(a : ℂ)‖ = a := by simp [abs_of_nonneg ha]
  have bnorm : ‖(b : ℂ)*phase t‖ = b := by
    simp [phase, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hb]
  constructor
  · simpa only [anorm, norm_neg, bnorm, sub_neg_eq_add] using
      abs_norm_sub_norm_le (a : ℂ) (-((b : ℂ)*phase t))
  · simpa only [anorm, bnorm] using norm_add_le (a : ℂ) ((b : ℂ)*phase t)

private theorem magnitude_subsequence (a b start target : ℝ) (wave : ℕ → ℂ)
    (error : Tendsto (fun j => wave j-((a : ℂ)+(b : ℂ)*phase (Real.log (j : ℝ)/2+start)))
      atTop (𝓝 0)) :
    ∃ degrees : ℕ → ℕ, Tendsto degrees atTop atTop ∧
      Tendsto (fun m => ‖wave (degrees m)‖) atTop (𝓝 ‖(a : ℂ)+(b : ℂ)*phase target‖) := by
  obtain ⟨degrees, large, phases⟩ := logarithmic_phase_subsequence start target
  refine ⟨degrees,large,?_⟩
  have modeled := (tendsto_const_nhds (x := (a : ℂ))).add
    ((tendsto_const_nhds (x := (b : ℂ))).mul phases)
  have restored := (error.comp large).add modeled
  rw [zero_add] at restored
  have converges : Tendsto (fun m => wave (degrees m)) atTop
      (𝓝 ((a : ℂ)+(b : ℂ)*phase target)) :=
    restored.congr fun m => sub_add_cancel _ _
  exact converges.norm

/-- The constructive and destructive envelope limits occur along integer
    subsequences whenever the complex remainder tends to zero. -/
theorem interference_envelopes_attained (a b start : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (wave : ℕ → ℂ)
    (error : Tendsto (fun j => wave j-((a : ℂ)+(b : ℂ)*phase (Real.log (j : ℝ)/2+start)))
      atTop (𝓝 0)) :
    (∃ degrees : ℕ → ℕ, Tendsto degrees atTop atTop ∧
      Tendsto (fun m => ‖wave (degrees m)‖) atTop (𝓝 (a+b))) ∧
    (∃ degrees : ℕ → ℕ, Tendsto degrees atTop atTop ∧
      Tendsto (fun m => ‖wave (degrees m)‖) atTop (𝓝 |a-b|)) := by
  constructor
  · have h := magnitude_subsequence a b start 0 wave error
    have upper : ‖(a : ℂ)+(b : ℂ)*phase 0‖ = a+b := by
      rw [show phase 0 = 1 by simp [phase], mul_one, ← Complex.ofReal_add,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (add_nonneg ha hb)]
    rwa [upper] at h
  · have h := magnitude_subsequence a b start Real.pi wave error
    have lower : ‖(a : ℂ)+(b : ℂ)*phase Real.pi‖ = |a-b| := by
      rw [show phase Real.pi = -1 from Complex.exp_pi_mul_I, mul_neg, mul_one,
        ← sub_eq_add_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rwa [lower] at h

theorem asymptotic_envelope_bounds (a b start : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (wave : ℕ → ℂ)
    (error : Tendsto (fun j => wave j-((a : ℂ)+(b : ℂ)*phase (Real.log (j : ℝ)/2+start)))
      atTop (𝓝 0)) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ j in atTop, |a-b|-epsilon ≤ ‖wave j‖ ∧ ‖wave j‖ ≤ a+b+epsilon := by
  filter_upwards [Metric.tendsto_nhds.mp error epsilon positive] with j close
  let t := Real.log (j : ℝ)/2+start
  let mode := (a : ℂ)+(b : ℂ)*phase t
  have e : ‖wave j-mode‖ < epsilon := by simpa only [dist_zero_right] using close
  have limits := two_term_magnitude_bounds a b t ha hb
  have norms := abs_le.mp ((abs_norm_sub_norm_le (wave j) mode).trans e.le)
  change |a-b| ≤ ‖mode‖ ∧ ‖mode‖ ≤ a+b at limits
  constructor <;> linarith [limits.1,limits.2,norms.1,norms.2]

def barrierPower (d : ℝ) : ℝ := 1/(1+Real.exp (Real.pi*(2*d-1)))

def balancedDetuning : ℝ := 1+Real.log (2/(Real.exp Real.pi-1))/Real.pi

theorem limiting_reflections_balance (d : ℝ) :
    barrierPower (d/2) = Real.sqrt (barrierPower d) ↔ d = balancedDetuning := by
  have positive (b : ℝ) : 0 ≤ barrierPower b := by unfold barrierPower; positivity
  have squared : barrierPower (d/2) = Real.sqrt (barrierPower d) ↔
      barrierPower (d/2)^2 = barrierPower d := by
    constructor
    · intro h
      rw [h,Real.sq_sqrt (positive d)]
    · intro h
      rw [← h,Real.sqrt_sq (positive (d/2))]
  let x := Real.exp (Real.pi*(d-1))
  let c := Real.exp Real.pi
  have xpositive : 0 < x := Real.exp_pos _
  have cpositive : 0 < c := Real.exp_pos _
  have c1 : 1 < c := by
    change 1 < Real.exp Real.pi
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr Real.pi_pos
  have p : barrierPower (d/2) = 1/(1+x) := by
    simp only [barrierPower, x, show 2*(d/2)-1 = d-1 by ring]
  have q : barrierPower d = 1/(1+c*x^2) := by
    have exponent : Real.exp (Real.pi*(2*d-1)) = c*x^2 := by
      dsimp [c,x]
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [barrierPower,exponent]
  have h1 : 1+x ≠ 0 := by positivity
  have h2 : 1+c*x^2 ≠ 0 := by positivity
  have algebra : (1/(1+x))^2 = 1/(1+c*x^2) ↔ (c-1)*x = 2 := by
    constructor
    · intro eq
      field_simp [h1,h2] at eq
      have vanish : ((c-1)*x-2)*x = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp vanish).resolve_right xpositive.ne')
    · intro eq
      have product := congrArg (fun y : ℝ => x*y) eq
      field_simp [h1,h2]
      nlinarith
  rw [squared,p,q,algebra,mul_comm (c-1) x,← eq_div_iff (sub_ne_zero.mpr c1.ne')]
  have rhs : 0 < 2/(c-1) := div_pos (by norm_num) (sub_pos.mpr c1)
  constructor
  · intro eq
    have logged := congrArg Real.log eq
    change Real.log (Real.exp (Real.pi*(d-1))) = Real.log (2/(c-1)) at logged
    rw [Real.log_exp] at logged
    have divided : d-1 = Real.log (2/(c-1))/Real.pi :=
      (eq_div_iff Real.pi_ne_zero).mpr (by simpa only [mul_comm] using logged)
    unfold balancedDetuning
    change d = 1+Real.log (2/(c-1))/Real.pi
    linarith
  · intro eq
    change d = 1+Real.log (2/(c-1))/Real.pi at eq
    change Real.exp (Real.pi*(d-1)) = 2/(c-1)
    have exponent : Real.pi*(d-1) = Real.log (2/(c-1)) := by
      rw [eq]
      field_simp [Real.pi_ne_zero]
      ring
    rw [exponent,Real.exp_log rhs]

#print axioms logarithmic_phase_subsequence
#print axioms two_term_magnitude_bounds
#print axioms interference_envelopes_attained
#print axioms asymptotic_envelope_bounds
#print axioms limiting_reflections_balance

end
end SchwarzschildMixtures.Strain.LightRing
