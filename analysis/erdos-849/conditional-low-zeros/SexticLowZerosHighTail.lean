import SexticLowZerosActual
import RSBounds.BacklundHighCount
import RSBounds.RosserTailIntegrals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Reciprocal weights above height 100 using the analytic Rosser bound

The multiplicity-copy and partial-summation argument follows
RSBounds.WeightedZetaZeros and RSBounds.RosserWeightedBounds (Apache-2.0,
revision 82d7a55f02e52cd071cd8ed800cc889a23ad3e61). The analytic zero-count
bound for heights at least 100 suffices on this interval.
-/

namespace ShortPrimeInterval.SexticTail.LowZeros

open Set MeasureTheory
open scoped BigOperators Interval
open TernaryGoldbach.RSBounds
open TernaryGoldbach.RSBounds.BacklundCountIdentity

private theorem height_ge_hundred : (100 : ℝ) ≤ height := by norm_num [height]
private theorem height_gt_zero : 0 < height := by norm_num [height]

private noncomputable def zeroCopies (B : ℝ) : Finset (Σ _ : ℂ, ℕ) := by
  classical
  exact (closedPositiveZeros B).sigma (fun ρ => Finset.range (analyticOrderAt riemannZeta ρ).toNat)

private theorem sum_copies (B : ℝ) (weight : ℂ → ℝ) :
    (∑ z ∈ zeroCopies B, weight z.1) =
      ∑ ρ ∈ closedPositiveZeros B, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * weight ρ := by
  classical
  simp [zeroCopies, Finset.sum_sigma, nsmul_eq_mul]

private theorem count_copies {t B : ℝ} (ht : 0 < t) (htB : t ≤ B) :
    ordinateCount (zeroCopies B) (fun z => z.1.im) t = N_le t := by
  classical
  have hfilter : (closedPositiveZeros B).filter (fun ρ => ρ.im ≤ t) = closedPositiveZeros t := by
    ext ρ
    rw [Finset.mem_filter, mem_closedPositiveZeros_iff (ht.trans_le htB), mem_closedPositiveZeros_iff ht]
    constructor
    · rintro ⟨⟨hz, hi, _⟩, hT⟩
      exact ⟨hz, hi, hT⟩
    · rintro ⟨hz, hi, hT⟩
      exact ⟨⟨hz, hi, hT.trans htB⟩, hT⟩
  unfold ordinateCount
  dsimp only
  rw [sum_copies B (fun ρ => if ρ.im ≤ t then (1 : ℝ) else 0)]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter]
  simp [N_le]

private theorem weight_copies :
    (∑ z ∈ zeroCopies height, if 100 < z.1.im ∧ z.1.im ≤ height then 1 / z.1.im else 0) =
      tailOrdinateMass (closedPositiveZeros height) := by
  classical
  rw [sum_copies height (fun ρ => if 100 < ρ.im ∧ ρ.im ≤ height then 1 / ρ.im else 0)]
  unfold tailOrdinateMass
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hi := ((mem_closedPositiveZeros_iff height_gt_zero).mp hρ).2.2
  simp only [hi, and_true, mul_ite, mul_one_div, mul_zero]

/-- The upper endpoint is inclusive, and all ordinates in the sum exceed 100. -/
theorem tailOrdinateMass_le_from_high_count :
    tailOrdinateMass (closedPositiveZeros height) ≤ reciprocalTailAllowance := by
  let a : ℝ := 100
  have ha : 0 < a := by norm_num [a]
  have hab : a ≤ height := height_ge_hundred
  have hpos (t : ℝ) (ht : t ∈ Icc a height) : 0 < t := ha.trans_le ht.1
  have hgt (t : ℝ) (ht : t ∈ Icc a height) : 1 < t := by
    have hlo : (100 : ℝ) ≤ t := ht.1
    linarith
  have hint (f : ℝ → ℝ) (hf : ∀ t ∈ Icc a height, ContinuousAt f t) :
      IntervalIntegrable f volume a height := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact fun t ht => (hf t ht).continuousWithinAt
  have hφ (t : ℝ) (ht : t ∈ Icc a height) : HasDerivAt (fun u : ℝ => 1 / u) (-1 / t ^ 2) t := by
    simpa only [one_div, neg_div, neg_mul, one_mul] using hasDerivAt_inv (hpos t ht).ne'
  have hF (t : ℝ) (ht : t ∈ Icc a height) := hasDerivAt_rosserF (hpos t ht)
  have hR (t : ℝ) (ht : t ∈ Icc a height) := hasDerivAt_rosserR 1.588 (hgt t ht)
  have hC (t : ℝ) (ht : t ∈ Icc a height) :
      |(N_le t : ℝ) - rosserF t| < rosserR 1.588 t :=
    rosser_bound_high ht.1
  have h := weighted_ordinate_sum_le_decreasing
    (zeroCopies height) (fun z => z.1.im) hab hφ hF hR
    (hint _ fun t ht => by have := hpos t ht; fun_prop (disch := positivity))
    (hint _ fun t ht => by have := hpos t ht; fun_prop (disch := positivity))
    (hint _ fun t ht => by
      have := hgt t ht
      have := Real.log_pos (hgt t ht)
      have := hpos t ht
      fun_prop (disch := positivity))
    (fun t _ => div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg t))
    (fun t ht => by
      rw [count_copies (hpos t ht) ht.2]
      linarith only [(abs_lt.mp (hC t ht)).2])
  rw [weight_copies, count_copies height_gt_zero le_rfl, count_copies ha hab] at h
  simp only [mul_one_div] at h
  have hUpper : ((N_le height : ℝ) - rosserF height - rosserR 1.588 height) / height ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (by linarith only [(abs_lt.mp (hC height ⟨hab, le_rfl⟩)).2]) height_gt_zero.le
  have hLower : (rosserF a + rosserR 1.588 a - (N_le a : ℝ)) / a ≤ 2 * rosserR 1.588 a / a :=
    div_le_div_of_nonneg_right (by linarith only [(abs_lt.mp (hC a ⟨le_rfl, hab⟩)).1]) ha.le
  have hintegral := RosserTailIntegrals.integral_density_div_le (a := a) (b := height) (by norm_num [a]) hab
  unfold reciprocalTailAllowance
  change (∫ t in a..height, RosserTailIntegrals.density t / t) +
      ((N_le height : ℝ) - rosserF height - rosserR 1.588 height) / height -
      ((N_le a : ℝ) - rosserF a - rosserR 1.588 a) / a ≥
        tailOrdinateMass (closedPositiveZeros height) at h
  have hneg : -(((N_le a : ℝ) - rosserF a - rosserR 1.588 a) / a) =
      (rosserF a + rosserR 1.588 a - (N_le a : ℝ)) / a := by ring
  rw [sub_eq_add_neg, hneg] at h
  change tailOrdinateMass (closedPositiveZeros height) ≤
    (Real.log (height / (2 * Real.pi)) ^ 2 - Real.log (a / (2 * Real.pi)) ^ 2) /
      (4 * Real.pi) + (0.137 + 0.443 / Real.log a) * (1 / a - 1 / height) +
      2 * rosserR 1.588 a / a
  linarith only [h, hUpper, hLower, hintegral]

end ShortPrimeInterval.SexticTail.LowZeros
