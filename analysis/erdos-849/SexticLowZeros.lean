import SexticTailBudget
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# The low-zero contribution to sixfold smoothing

The coefficient is the sixth forward difference of the sixth primitive
of `t ↦ t^ρ / ρ`, divided by `h^6`. The lower average starts at `x - 6h`.
The repeated integration argument follows RSBounds' PolynomialZeroKernel
(Apache-2.0, revision 82d7a55f02e52cd071cd8ed800cc889a23ad3e61).
-/

namespace ShortPrimeInterval.SexticTail.LowZeros

open MeasureTheory Set
open scoped Interval BigOperators ComplexConjugate

/-- The real-part statement of finite-height RH needed for this bound. -/
def FiniteRH (H : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2

/-- Import the strict cutoff in the published finite-height statement. -/
theorem finiteRH_of_strictCutoff {H T : ℝ} (hHT : H < T)
    (published : ∀ ρ : ℂ, riemannZeta ρ = 0 →
      (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → |ρ.im| < T → ρ.re = 1 / 2) :
    FiniteRH H := by
  intro ρ hz h0 h1 hheight
  apply published ρ hz _ _ (hheight.trans_lt hHT)
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro hone
    simp [hone] at h1

def forwardDiff (h : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | n + 1, f => fun x => forwardDiff h n f (x + h) - forwardDiff h n f x

noncomputable def iteratedIntegral (h : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | n + 1, f => fun x => ∫ u in 0..h, iteratedIntegral h n f (x + u)

def rising (ρ : ℂ) : ℕ → ℂ
  | 0 => ρ
  | n + 1 => rising ρ n * (ρ + (n + 1 : ℕ))

noncomputable def primitive (ρ : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (ρ + n) / rising ρ n

noncomputable def zeroCoefficient (x h : ℝ) (ρ : ℂ) : ℂ :=
  forwardDiff h 6 (primitive ρ 6) x / (h : ℂ) ^ 6

noncomputable def coefficient (lower : Bool) (x : ℝ) (ρ : ℂ) : ℂ :=
  let h := step * x
  zeroCoefficient (if lower then x - 6 * h else x) h ρ

private theorem hasDerivAt_primitive {ρ : ℂ} (hρ : 0 < ρ.re)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (primitive ρ (n + 1)) (primitive ρ n x) x := by
  have hr : ρ + (n : ℂ) ≠ -1 := by
    intro heq
    have he := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re, Complex.one_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd := (hasDerivAt_ofReal_cpow_const' hx.ne' hr).div_const (rising ρ n)
  have hfun : (fun t : ℝ => (t : ℂ) ^ (ρ + n + 1) / (ρ + n + 1) / rising ρ n) =
      primitive ρ (n + 1) := by
    funext t
    simp only [primitive, rising, Nat.cast_add, Nat.cast_one, add_assoc, div_div]
    congr 1
    ring
  rw [hfun] at hd
  exact hd

private theorem hasDerivAt_forwardDiff {h : ℝ} (hh : 0 ≤ h) {F f : ℝ → ℂ}
    (hF : ∀ x, 0 < x → HasDerivAt F (f x) x) (n : ℕ) :
    ∀ x, 0 < x → HasDerivAt (forwardDiff h n F) (forwardDiff h n f x) x := by
  induction n with
  | zero => exact hF
  | succ n inductionHypothesis =>
    intro x hx
    have shifted := (inductionHypothesis (x + h) (by linarith)).scomp x
      ((hasDerivAt_id x).add_const h)
    have hfun : (forwardDiff h n F ∘ fun y => id y + h) - forwardDiff h n F =
        forwardDiff h (n + 1) F := rfl
    simpa only [hfun, forwardDiff, one_smul] using shifted.sub (inductionHypothesis x hx)

private theorem forwardDiff_primitive_eq_integral {ρ : ℂ} (hρ : 0 < ρ.re)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ∀ x, 0 < x →
      forwardDiff h n (primitive ρ n) x =
        iteratedIntegral h n (fun t : ℝ => (t : ℂ) ^ ρ / ρ) x := by
  induction n with
  | zero => intro x _; simp [forwardDiff, iteratedIntegral, primitive, rising]
  | succ n inductionHypothesis =>
    intro x hx
    let g := fun u : ℝ => forwardDiff h n (primitive ρ (n + 1)) (x + u)
    have derivative (u : ℝ) (hu : u ∈ uIcc 0 h) :
        HasDerivAt g (forwardDiff h n (primitive ρ n) (x + u)) u := by
      rw [uIcc_of_le hh] at hu
      simpa only [g, Function.comp_def, one_smul] using
        (hasDerivAt_forwardDiff hh (fun t ht => hasDerivAt_primitive hρ n ht) n
          (x + u) (by linarith [hu.1])).scomp u ((hasDerivAt_id u).const_add x)
    have integrable : IntervalIntegrable
        (fun u : ℝ => forwardDiff h n (primitive ρ n) (x + u)) volume 0 h := by
      apply ContinuousOn.intervalIntegrable
      intro u hu
      rw [uIcc_of_le hh] at hu
      -- The derivative integrand is itself a forward difference of primitives.
      have hcont : ContinuousAt (forwardDiff h n (primitive ρ n)) (x + u) := by
        cases n with
        | zero =>
          have hr : ρ ≠ 0 := by
            intro hz
            simp [hz] at hρ
          have hfun : primitive ρ 0 = fun t : ℝ => (t : ℂ) ^ ρ / ρ := by
            funext t
            simp only [primitive, rising, Nat.cast_zero, add_zero]
          rw [forwardDiff, hfun]
          exact ((hasDerivAt_ofReal_cpow_const
            (by linarith [hu.1] : x + u ≠ 0) hr).div_const ρ).continuousAt
        | succ k =>
          exact (hasDerivAt_forwardDiff hh
            (fun t ht => hasDerivAt_primitive hρ k ht) (k + 1) (x + u)
              (by linarith [hu.1])).continuousAt
      exact (hcont.comp (continuousAt_id.const_add x)).continuousWithinAt
    calc
      _ = g h - g 0 := by simp [g, forwardDiff]
      _ = ∫ u in 0..h, forwardDiff h n (primitive ρ n) (x + u) :=
        (intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable).symm
      _ = _ := by
        simp only [iteratedIntegral]
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hh] at hu
        exact inductionHypothesis (x + u) (by linarith [hu.1])

private theorem integral_affine (a b h : ℝ) :
    (∫ u in 0..h, a + b * u) = a * h + b * h ^ 2 / 2 := by
  have ha : IntervalIntegrable (fun _ : ℝ => a) volume 0 h :=
    continuous_const.intervalIntegrable 0 h
  have hb : IntervalIntegrable (fun u : ℝ => b * u) volume 0 h :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 h
  rw [intervalIntegral.integral_add ha hb, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

private theorem norm_iteratedIntegral_le_affine_on_window {h : ℝ} (hh : 0 ≤ h)
    (f : ℝ → ℂ) (a b : ℝ) (n : ℕ) :
    ∀ x, (∀ t ∈ Icc x (x + (n : ℝ) * h), ‖f t‖ ≤ a + b * t) →
      ‖iteratedIntegral h n f x‖ ≤ h ^ n * (a + b * x + b * (n : ℝ) * h / 2) := by
  induction n with
  | zero =>
    intro x hbound
    simpa [iteratedIntegral] using hbound x (by simp)
  | succ n inductionHypothesis =>
    intro x hbound
    let majorant := fun u : ℝ => h ^ n * (a + b * (x + u) + b * (n : ℝ) * h / 2)
    have hmajorant : ∀ᵐ u : ℝ, u ∈ Ioc 0 h →
        ‖iteratedIntegral h n f (x + u)‖ ≤ majorant u := by
      filter_upwards [] with u hu
      apply inductionHypothesis
      intro t ht
      exact hbound t ⟨by linarith [ht.1, hu.1], by
        push_cast
        linarith [ht.2, hu.2]⟩
    have hc : Continuous majorant := by unfold majorant; fun_prop
    change ‖∫ u in 0..h, iteratedIntegral h n f (x + u)‖ ≤ _
    apply (intervalIntegral.norm_integral_le_of_norm_le hh hmajorant
      (hc.intervalIntegrable 0 h)).trans_eq
    have heq : majorant =
        fun u => h ^ n * ((a + b * x + b * (n : ℝ) * h / 2) + b * u) := by
      funext u
      unfold majorant
      ring
    rw [heq, intervalIntegral.integral_const_mul, integral_affine]
    push_cast
    ring

private theorem norm_zeroCoefficient_le {x h a b : ℝ} (hx : 0 < x) (hh : 0 < h)
    {ρ : ℂ} (hρ : 0 < ρ.re)
    (hbound : ∀ t ∈ Icc x (x + 6 * h), ‖(t : ℂ) ^ ρ / ρ‖ ≤ a + b * t) :
    ‖zeroCoefficient x h ρ‖ ≤ a + b * x + 3 * b * h := by
  rw [zeroCoefficient, forwardDiff_primitive_eq_integral hρ hh.le 6 x hx,
    norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply (div_le_iff₀ (pow_pos hh 6)).2
  refine (norm_iteratedIntegral_le_affine_on_window hh.le _ a b 6 x ?_).trans_eq ?_
  · simpa using hbound
  · push_cast
    ring

private theorem norm_zero_integrand {t : ℝ} (ht : 0 < t)
    {ρ : ℂ} (hr : ρ.re = 1 / 2) :
    ‖(t : ℂ) ^ ρ / ρ‖ = Real.sqrt t / ‖ρ‖ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht, hr, Real.sqrt_eq_rpow]

/-- The lower window only uses points to the left of `x`. -/
theorem norm_lower_le {x h : ℝ} (hh : 0 < h) (hleft : 0 < x - 6 * h)
    {ρ : ℂ} (hr : ρ.re = 1 / 2) :
    ‖zeroCoefficient (x - 6 * h) h ρ‖ ≤ Real.sqrt x / ‖ρ‖ := by
  have hb : ∀ t ∈ Icc (x - 6 * h) (x - 6 * h + 6 * h),
      ‖(t : ℂ) ^ ρ / ρ‖ ≤ Real.sqrt x / ‖ρ‖ + 0 * t := by
    intro t ht
    rw [norm_zero_integrand (hleft.trans_le ht.1) hr, zero_mul, add_zero]
    exact div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt (by linarith [ht.2])) (norm_nonneg ρ)
  simpa using norm_zeroCoefficient_le hleft hh (by rw [hr]; norm_num) hb

/-- The mean displacement of the upper sixfold window is `3h`. -/
theorem norm_upper_le {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {ρ : ℂ}
    (hr : ρ.re = 1 / 2) :
    ‖zeroCoefficient x h ρ‖ ≤ (1 + 3 * (h / x)) * Real.sqrt x / ‖ρ‖ := by
  let slope := Real.sqrt x / (x * ‖ρ‖)
  have hn : ρ ≠ 0 := by
    intro hz
    norm_num [hz] at hr
  have hn0 := norm_pos_iff.mpr hn
  have hb : ∀ t ∈ Icc x (x + 6 * h), ‖(t : ℂ) ^ ρ / ρ‖ ≤ 0 + slope * t := by
    intro t ht
    have ht0 := hx.trans_le ht.1
    have hs : Real.sqrt x ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
    have hprod := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg t)
    rw [← pow_two, Real.sq_sqrt ht0.le] at hprod
    have hsqrt : Real.sqrt t * x ≤ Real.sqrt x * t := by
      calc
        _ = Real.sqrt t * (Real.sqrt x ^ 2) := by rw [Real.sq_sqrt hx.le]
        _ = (Real.sqrt t * Real.sqrt x) * Real.sqrt x := by ring
        _ ≤ t * Real.sqrt x := mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg x)
        _ = _ := mul_comm _ _
    rw [norm_zero_integrand ht0 hr, zero_add]
    dsimp only [slope]
    rw [div_mul_eq_mul_div]
    rw [div_le_div_iff₀ hn0 (mul_pos hx hn0)]
    nlinarith only [mul_le_mul_of_nonneg_right hsqrt hn0.le]
  apply (norm_zeroCoefficient_le hx hh (by rw [hr]; norm_num) hb).trans_eq
  unfold slope
  field_simp [hx.ne', hn0.ne']
  ring

theorem norm_coefficient_le (lower : Bool) {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hr : ρ.re = 1 / 2) :
    ‖coefficient lower x ρ‖ ≤ (1 + 3 * step) * Real.sqrt x / ‖ρ‖ := by
  have hh : 0 < step * x := mul_pos (by norm_num [step]) hx
  cases lower with
  | false =>
    simpa [coefficient, hx.ne'] using norm_upper_le hx hh hr
  | true =>
    have hleft : 0 < x - 6 * (step * x) := by
      rw [show x - 6 * (step * x) = (1 - 6 * step) * x by ring]
      exact mul_pos (by norm_num [step]) hx
    refine (norm_lower_le hh hleft hr).trans ?_
    apply div_le_div_of_nonneg_right _ (norm_nonneg ρ)
    nlinarith only [mul_nonneg (by norm_num [step] : 0 ≤ 3 * step) (Real.sqrt_nonneg x)]

noncomputable def positiveReciprocalMass (zeros : Finset ℂ) : ℝ :=
  ∑ ρ ∈ zeros, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖

/-- This is RSBounds' reciprocal weight on the interval `(100,height]`. -/
noncomputable def tailOrdinateMass (zeros : Finset ℂ) : ℝ :=
  ∑ ρ ∈ zeros, if 100 < ρ.im then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im else 0

noncomputable def reciprocalTailAllowance : ℝ :=
  (Real.log (height / (2 * Real.pi)) ^ 2 - Real.log (100 / (2 * Real.pi)) ^ 2) /
      (4 * Real.pi) +
    (0.137 + 0.443 / Real.log 100) * (1 / 100 - 1 / height) +
    2 * (0.137 * Real.log 100 + 0.443 * Real.log (Real.log 100) + 1.588) / 100

private theorem split_positiveReciprocalMass (zeros : Finset ℂ) :
    positiveReciprocalMass zeros =
      positiveReciprocalMass (zeros.filter (fun ρ => ρ.im ≤ 100)) +
      ∑ ρ ∈ zeros, if 100 < ρ.im then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖ else 0 := by
  simp only [positiveReciprocalMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  rcases le_or_gt ρ.im 100 with h | h
  · simp [h, not_lt_of_ge h]
  · simp [h, not_le_of_gt h]

theorem positiveReciprocalMass_le_split (zeros : Finset ℂ) :
    positiveReciprocalMass zeros ≤
      positiveReciprocalMass (zeros.filter (fun ρ => ρ.im ≤ 100)) + tailOrdinateMass zeros := by
  have hnormTail :
      (∑ ρ ∈ zeros, if 100 < ρ.im then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖
        else 0) ≤ tailOrdinateMass zeros := by
    unfold tailOrdinateMass
    apply Finset.sum_le_sum
    intro ρ _
    split_ifs with h
    · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith)
        ((le_abs_self _).trans (Complex.abs_im_le_norm ρ))
    · rfl
  rw [split_positiveReciprocalMass]
  exact add_le_add le_rfl hnormTail

theorem scaledReciprocalMass_le (zeros : Finset ℂ)
    (hhead : positiveReciprocalMass (zeros.filter (fun ρ => ρ.im ≤ 100)) ≤ 0.592316)
    (htail : tailOrdinateMass zeros ≤ reciprocalTailAllowance) :
    2 * (1 + 3 * step) * positiveReciprocalMass zeros ≤ lowWeight := by
  have hmass := (positiveReciprocalMass_le_split zeros).trans (add_le_add hhead htail)
  have hbudget : 2 * (1 + 3 * step) * (0.592316 + reciprocalTailAllowance) = lowWeight := by
    let mainTerm := (Real.log (height / (2 * Real.pi)) ^ 2 -
      Real.log (100 / (2 * Real.pi)) ^ 2) / (4 * Real.pi)
    let integralError := (0.137 + 0.443 / Real.log 100) * (1 / 100 - 1 / height)
    let endpointError := 2 * (0.137 * Real.log 100 + 0.443 * Real.log (Real.log 100) + 1.588) / 100
    change 2 * (1 + 3 * step) * (0.592316 + (mainTerm + integralError + endpointError)) =
      2 * (1 + 3 * step) * (0.592316 + mainTerm + integralError + endpointError)
    ring
  exact (mul_le_mul_of_nonneg_left hmass (by norm_num [step])).trans_eq hbudget

noncomputable def pairedContribution (zeros : Finset ℂ) (lower : Bool) (x : ℝ) : ℂ :=
  ∑ ρ ∈ zeros, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
    (coefficient lower x ρ + coefficient lower x (conj ρ))

/-- The two conjugate ordinates contribute one pair with the same multiplicity. -/
theorem norm_pairedContribution_le_of_scaled_mass (zeros : Finset ℂ) (lower : Bool) {x : ℝ}
    (hx : 0 < x) (hRH : FiniteRH height)
    (hzeros : ∀ ρ ∈ zeros, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      0 < ρ.im ∧ ρ.im ≤ height)
    (hmass : 2 * (1 + 3 * step) * positiveReciprocalMass zeros ≤ 30) :
    ‖pairedContribution zeros lower x‖ ≤ 30 * Real.sqrt x := by
  unfold pairedContribution
  calc
    _ ≤ ∑ ρ ∈ zeros, ‖((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
        (coefficient lower x ρ + coefficient lower x (conj ρ))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ zeros, Real.sqrt x * (2 * (1 + 3 * step) *
        (((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖)) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hz, hre0, hre1, him0, himH⟩ := hzeros ρ hρ
      have hr := hRH ρ hz hre0 hre1 (by rwa [abs_of_pos him0])
      have hc : (conj ρ).re = 1 / 2 := by simpa using hr
      have primary := norm_coefficient_le lower hx hr
      have reflected := norm_coefficient_le lower hx hc
      rw [Complex.norm_conj] at reflected
      rw [norm_mul, Complex.norm_natCast]
      refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add primary reflected)) (Nat.cast_nonneg _)).trans_eq ?_
      ring
    _ = Real.sqrt x * (2 * (1 + 3 * step) * positiveReciprocalMass zeros) := by
      simp only [positiveReciprocalMass, Finset.mul_sum]
    _ ≤ Real.sqrt x * 30 :=
      mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

theorem norm_pairedContribution_le (zeros : Finset ℂ) (lower : Bool) {x : ℝ}
    (hx : 0 < x) (hRH : FiniteRH height)
    (hzeros : ∀ ρ ∈ zeros, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      0 < ρ.im ∧ ρ.im ≤ height)
    (hmass : 2 * (1 + 3 * step) * positiveReciprocalMass zeros ≤ lowWeight) :
    ‖pairedContribution zeros lower x‖ ≤ 30 * Real.sqrt x :=
  norm_pairedContribution_le_of_scaled_mass zeros lower hx hRH hzeros (hmass.trans lowWeight_le)

/-- The low-zero bound using the published head and reciprocal-tail estimates. -/
theorem norm_pairedContribution_le_of_rosser (zeros : Finset ℂ) (lower : Bool) {x : ℝ}
    (hx : 0 < x) (hRH : FiniteRH height)
    (hzeros : ∀ ρ ∈ zeros, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      0 < ρ.im ∧ ρ.im ≤ height)
    (hhead : positiveReciprocalMass (zeros.filter (fun ρ => ρ.im ≤ 100)) ≤ 0.592316)
    (htail : tailOrdinateMass zeros ≤ reciprocalTailAllowance) :
    ‖pairedContribution zeros lower x‖ ≤ 30 * Real.sqrt x :=
  norm_pairedContribution_le zeros lower hx hRH hzeros (scaledReciprocalMass_le zeros hhead htail)

end ShortPrimeInterval.SexticTail.LowZeros
