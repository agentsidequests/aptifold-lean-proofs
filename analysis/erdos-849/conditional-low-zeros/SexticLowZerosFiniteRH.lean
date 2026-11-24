import SexticLowZerosHighTail
import SexticLowZerosMoment

/-!
# The sixfold low-zero bound with finite-height RH as its only analytic hypothesis

The available numerical margin permits the coarse xi-moment head bound
and the Rosser tail bound for heights at least 100.
-/

namespace ShortPrimeInterval.SexticTail.LowZeros

open scoped BigOperators
open TernaryGoldbach.Explicit
open TernaryGoldbach.RSBounds
open TernaryGoldbach.RSBounds.BacklundCountIdentity

private theorem log_cutoff_le : Real.log (height / (2 * Real.pi)) ≤ 12.7 := by
  have hle : height / (2 * Real.pi) ≤ 315000 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num [height]
    linarith [Real.pi_gt_three]
  have h0 : 0 < height / (2 * Real.pi) := by norm_num [height, Real.pi_pos]
  have hpow : (height / (2 * Real.pi)) ^ 10 ≤ Real.exp 1 ^ 127 :=
    (pow_le_pow_left₀ h0.le hle 10).trans
      ((by norm_num : (315000 : ℝ) ^ 10 ≤ (2.7182818283 : ℝ) ^ 127).trans
        (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 127))
  have h := Real.log_le_log (by positivity : 0 < (height / (2 * Real.pi)) ^ 10) hpow
  rw [Real.log_pow, Real.log_pow, Real.log_exp] at h
  norm_num at h
  linarith

private theorem log_hundred_ge : (2.5 : ℝ) ≤ Real.log (100 / (2 * Real.pi)) := by
  have hle : (25 / 2 : ℝ) ≤ 100 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four]
  have hpow : Real.exp 1 ^ 5 ≤ (100 / (2 * Real.pi)) ^ 2 :=
    (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5).trans
      ((by norm_num : (2.7182818286 : ℝ) ^ 5 ≤ (25 / 2 : ℝ) ^ 2).trans
        (pow_le_pow_left₀ (by norm_num) hle 2))
  have h := Real.log_le_log (by positivity : 0 < Real.exp 1 ^ 5) hpow
  rw [Real.log_pow, Real.log_exp, Real.log_pow] at h
  norm_num at h
  linarith

private theorem reciprocalTailAllowance_le : reciprocalTailAllowance ≤ 13.1 := by
  have hge : 1 ≤ height / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    norm_num [height]
    linarith [Real.pi_lt_four]
  have hU := pow_le_pow_left₀ (Real.log_nonneg hge) log_cutoff_le 2
  have hL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.5) log_hundred_ge 2
  have hmain :
      (Real.log (height / (2 * Real.pi)) ^ 2 - Real.log (100 / (2 * Real.pi)) ^ 2) /
      (4 * Real.pi) ≤ 12.92 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hU, hL, Real.pi_gt_three]
  have hlog : (1 : ℝ) ≤ Real.log 100 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hfactor : 0.137 + 0.443 / Real.log 100 ≤ (0.58 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.443) zero_lt_one hlog
    norm_num at h
    linarith
  have hsmall : (0.137 + 0.443 / Real.log 100) * (1 / 100 - 1 / height) ≤ (0.0058 : ℝ) := by
    calc
      _ ≤ 0.58 * (1 / 100 - 1 / height) :=
        mul_le_mul_of_nonneg_right hfactor (by norm_num [height])
      _ ≤ _ := by norm_num [height]
  have herr : 2 * rosserR 1.588 100 / 100 ≤ 0.08 := by linarith [rosserR_hundred_le]
  change (Real.log (height / (2 * Real.pi)) ^ 2 - Real.log (100 / (2 * Real.pi)) ^ 2) /
      (4 * Real.pi) + (0.137 + 0.443 / Real.log 100) * (1 / 100 - 1 / height) +
      2 * rosserR 1.588 100 / 100 ≤ 13.1
  linarith only [hmain, hsmall, herr]

private theorem scaled_head_and_tail_le (hRH : FiniteRH height) :
    2 * (1 + 3 * step) * positiveReciprocalMass (closedPositiveZeros height) ≤ 30 := by
  have hm := positiveReciprocalMass_le_split (closedPositiveZeros height)
  rw [closed_head] at hm
  have h := hm.trans (add_le_add (positiveReciprocalMass_head_le_from_moment hRH)
    (tailOrdinateMass_le_from_high_count.trans reciprocalTailAllowance_le))
  calc
    _ ≤ 2 * (1 + 3 * step) * (1.85 + 13.1) :=
      mul_le_mul_of_nonneg_left h (by norm_num [step])
    _ ≤ _ := by norm_num [step]

/-- The actual low-zero term, conditional only on finite-height RH. -/
theorem norm_lowZeroSum_le (lower : Bool) {x : ℝ} (hx : 0 < x) (hRH : FiniteRH height) :
    ‖∑ ρ ∈ lowZeros, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * coefficient lower x ρ‖ ≤
      30 * Real.sqrt x :=
  norm_lowZeroSum_le_of_scaled_mass lower hx hRH (scaled_head_and_tail_le hRH)

/-- The low portion of every finite contour above the cutoff, in either window. -/
theorem norm_rect_lowZeroSum_le (lower : Bool) {x T : ℝ} (hx : 0 < x)
    (hT : height < T) (hRH : FiniteRH height) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ height),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤ 30 * Real.sqrt x := by
  rw [rect_lowZeroSum_eq lower x hT]
  exact norm_lowZeroSum_le lower hx hRH

end ShortPrimeInterval.SexticTail.LowZeros
