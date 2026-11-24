import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A scalar budget for the prime-interval tail

These are arithmetic bounds for sixfold RSBounds smoothing at a new step
and zero height. Applying the adapted analytic bounds to Chebyshev's psi
requires a separate proof. The final theorem consumes that bound as a premise.
-/

namespace ShortPrimeInterval.SexticTail

open Real

def height : ℝ := 1890000
noncomputable def step : ℝ := 1 / 130000

private noncomputable def countError (t : ℝ) : ℝ :=
  0.137 * log t + 0.443 * log (log t) + 1.588

private theorem pow_lower_exp (n : ℕ) : (2.7 : ℝ) ^ n ≤ exp (n : ℝ) := by
  simpa [Real.exp_nat_mul] using
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (by linarith [exp_one_gt_d9] : (2.7 : ℝ) ≤ exp 1) n

private theorem log_height_div_two_pi :
    0 ≤ log (height / (2 * π)) ∧ log (height / (2 * π)) ≤ 13 := by
  have hden : (0 : ℝ) < 2 * π := by positivity
  have hratio : (1 : ℝ) ≤ height / (2 * π) := by
    apply (le_div_iff₀ hden).2
    linarith [pi_lt_four, show height = 1890000 by rfl]
  refine ⟨log_nonneg hratio, le_of_lt ?_⟩
  apply (log_lt_iff_lt_exp (by linarith : 0 < height / (2 * π))).2
  calc
    height / (2 * π) ≤ 1890000 / 6 := by
      unfold height
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_gt_three])
    _ < (2.7 : ℝ) ^ 13 := by norm_num
    _ ≤ exp 13 := pow_lower_exp 13

private theorem log_and_count_bounds {t : ℝ} (ht : 100 ≤ t) (hth : t ≤ height) :
    1 ≤ log t ∧ countError t ≤ 6 := by
  have ht0 : 0 < t := by linarith
  have htlog : 1 ≤ log t :=
    (Real.le_log_iff_exp_le ht0).2 (by linarith [exp_one_lt_three])
  have hlog17 : log t < 17 := (log_lt_iff_lt_exp ht0).2
    (hth.trans_lt ((show height < (2.7 : ℝ) ^ 17 by norm_num [height]).trans_le
      (pow_lower_exp 17)))
  have hloglog : log (log t) < 3 :=
    (log_lt_iff_lt_exp (by linarith : 0 < log t)).2
      (hlog17.trans ((show (17 : ℝ) < 2.7 ^ 3 by norm_num).trans_le (pow_lower_exp 3)))
  exact ⟨htlog, by unfold countError; linarith⟩

/-- Twice the reciprocal-weight bound for the positive ordinates through the chosen height.
    The first term is the upstream bound on the first 100 units of height. -/
noncomputable def lowWeight : ℝ :=
  2 * (1 + 3 * step) *
    (0.592316 +
      (log (height / (2 * π)) ^ 2 - log (100 / (2 * π)) ^ 2) / (4 * π) +
      (0.137 + 0.443 / log 100) * (1 / 100 - 1 / height) + 2 * countError 100 / 100)

theorem lowWeight_le : lowWeight ≤ 30 := by
  have hlo := log_height_div_two_pi
  have hs : log (height / (2 * π)) ^ 2 ≤ (13 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlo.1 hlo.2 2
  have hlog100 := log_and_count_bounds (t := 100) le_rfl (by norm_num [height])
  have hpart :
      (log (height / (2 * π)) ^ 2 - log (100 / (2 * π)) ^ 2) / (4 * π) ≤ 169 / 12 := by
    calc
      _ ≤ 169 / (4 * π) := div_le_div_of_nonneg_right
        (by linarith [sq_nonneg (log (100 / (2 * π)))]) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_gt_three])
  have hcoeff : 0.137 + 0.443 / log 100 ≤ (0.58 : ℝ) := by
    have ht : (0.443 : ℝ) / log 100 ≤ 0.443 :=
      (div_le_iff₀ (by linarith : 0 < log 100)).2 (by linarith [hlog100.1])
    linarith
  have hcorrection :
      (0.137 + 0.443 / log 100) * (1 / 100 - 1 / height) ≤ (0.58 : ℝ) / 100 := by
    calc
      _ ≤ 0.58 * (1 / 100 - 1 / height) :=
        mul_le_mul_of_nonneg_right hcoeff (by norm_num [height])
      _ ≤ _ := by norm_num [height]
  calc
    lowWeight ≤ 2 * (1 + 3 * step) * (0.592316 + 169 / 12 + 0.58 / 100 + 2 * 6 / 100) := by
      unfold lowWeight
      exact mul_le_mul_of_nonneg_left (by linarith only [hpart, hcorrection, hlog100.2])
        (by norm_num [step])
    _ ≤ 30 := by norm_num [step]

private noncomputable def fifthTail : ℝ :=
  (log (height / (2 * π)) / 4 + 1 / 16) / (2 * π * height ^ 4) +
    0.137 / (5 * height ^ 5) + 0.443 / (5 * height ^ 5 * log height) +
    2 * countError height / height ^ 5

/-- For an ordinate t above the cutoff, t⁻⁷ ≤ t⁻⁵ / height².
    This uses the upstream fifth-reciprocal sum and the sixfold numerator bound. -/
noncomputable def highWeight : ℝ :=
  (64 * (1 + 6 * step) ^ 7 / step ^ 6) * (fifthTail / height ^ 2)

theorem highWeight_le : highWeight ≤ 39 / 10000000 := by
  have hh := log_and_count_bounds (t := height) (by norm_num [height]) le_rfl
  have hmain :
      (log (height / (2 * π)) / 4 + 1 / 16) / (2 * π * height ^ 4) ≤
        (13 / 4 + 1 / 16) / (6 * height ^ 4) := by
    calc
      _ ≤ (13 / 4 + 1 / 16) / (2 * π * height ^ 4) :=
        div_le_div_of_nonneg_right (by linarith [log_height_div_two_pi.2])
          (by positivity [show 0 < height by norm_num [height]])
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num [height])
        (mul_le_mul_of_nonneg_right (by linarith [pi_gt_three]) (by positivity))
  have hlog :
      (0.443 : ℝ) / (5 * height ^ 5 * log height) ≤ 0.443 / (5 * height ^ 5) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num [height]) ?_
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hh.1 (by norm_num [height] : 0 ≤ 5 * height ^ 5)
  have htail : fifthTail ≤ (0.56 : ℝ) / height ^ 4 := by
    unfold fifthTail
    have herr := mul_le_mul_of_nonneg_right hh.2 (by norm_num [height] : 0 ≤ 2 / height ^ 5)
    norm_num [height] at hmain hlog herr ⊢
    linarith
  have hkernel : 64 * (1 + 6 * step) ^ 7 / step ^ 6 ≤ 65 / step ^ 6 := by
    norm_num [step]
  calc
    highWeight ≤ (64 * (1 + 6 * step) ^ 7 / step ^ 6) *
        (((0.56 : ℝ) / height ^ 4) / height ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htail (sq_nonneg height))
        (by norm_num [step])
    _ ≤ (65 / step ^ 6) * (((0.56 : ℝ) / height ^ 4) / height ^ 2) :=
      mul_le_mul_of_nonneg_right hkernel (by norm_num [height])
    _ ≤ _ := by norm_num [height, step]

private theorem sqrt_lower {x : ℝ} (hx : 400000000000000 ≤ x) :
    20000000 ≤ sqrt x := by
  calc
    (20000000 : ℝ) = sqrt ((20000000 : ℝ) ^ 2) := (sqrt_sq (by norm_num)).symm
    _ ≤ sqrt x := sqrt_le_sqrt (by linarith : (20000000 : ℝ) ^ 2 ≤ x)

private theorem sqrt_scale {x : ℝ} (hx : 400000000000000 ≤ x) :
    20000000 * sqrt x ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ sqrt x * sqrt x := mul_le_mul_of_nonneg_right (sqrt_lower hx) (sqrt_nonneg _)
    _ = x := mul_self_sqrt hx0

/-- Integral allowance for the positive half of the left contour majorant,
    split at ordinates 1 and 2^17. -/
theorem leftMajorant_mass_le :
    748 + 1430 * log 131072 + 91 * (1300 / 6 + 80 / 5) ≤ (40000 : ℝ) := by
  have hlog : log 131072 ≤ 12 := by
    rw [show (131072 : ℝ) = 2 ^ (17 : ℕ) by norm_num, log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_lt_d9]
  linarith

/-- A bound of 40000/(π√x) on the absolute left remainder fits the budget. -/
theorem leftRemainder_le_one {x : ℝ} (hx : 400000000000000 ≤ x) :
    40000 / (π * sqrt x) ≤ (1 : ℝ) := by
  have hroot := sqrt_lower hx
  have hden : 0 < π * sqrt x := mul_pos pi_pos (by linarith)
  have hprod := mul_le_mul_of_nonneg_right (le_of_lt pi_gt_three) (sqrt_nonneg x)
  exact (div_le_iff₀ hden).2 (by linarith)

/-- A left-contour remainder of at most one suffices for the 29 ppm budget. -/
theorem budget_le {x : ℝ} (hx : 400000000000000 ≤ x) :
    sqrt x * lowWeight + (x + 1) * highWeight + 1 + log (2 * π) + 3 * step * x
      ≤ (29 / 1000000 : ℝ) * x := by
  have hlog : log (2 * π) ≤ 3 := by
    apply le_of_lt
    apply (log_lt_iff_lt_exp (by positivity : 0 < 2 * π)).2
    exact (show 2 * π < (2.7 : ℝ) ^ 3 by
      nlinarith [pi_lt_four]).trans_le (pow_lower_exp 3)
  have hlo := mul_le_mul_of_nonneg_left lowWeight_le (sqrt_nonneg x)
  have hhi := mul_le_mul_of_nonneg_left highWeight_le (by linarith : 0 ≤ x + 1)
  norm_num [step]
  linarith [sqrt_scale hx]

private theorem small_root_le {x : ℝ} (hx : 400000000000000 ≤ x) :
    x ^ (1 / 3 : ℝ) ≤ sqrt x / 20 := by
  have hx0 : 0 < x := by linarith
  have hroot : (20 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    have h := rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 20 ^ (6 : ℕ))
      (by linarith : (20 : ℝ) ^ (6 : ℕ) ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 20)] at h
    norm_num at h
    exact h
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20), sqrt_eq_rpow]
  calc
    _ ≤ x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by rw [← rpow_add hx0]; congr 1; norm_num

/-- The prime-power correction uses the pinned Mathlib bounds directly. -/
theorem psi_sub_theta_le {x : ℝ} (hx : 400000000000000 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 6 * sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : log 4 + 4 ≤ (5.4 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
    linarith [log_two_lt_d9]
  have hpsi {t : ℝ} (ht : 0 ≤ t) : Chebyshev.psi t ≤ 5.4 * t :=
    (Chebyshev.psi_le_const_mul_self ht).trans (mul_le_mul_of_nonneg_right hlog ht)
  have hthree := small_root_le hx
  have hfive : x ^ (1 / 5 : ℝ) ≤ sqrt x / 20 :=
    (rpow_le_rpow_of_exponent_le hx1 (by norm_num)).trans hthree
  have hhalf : x ^ (2 : ℝ)⁻¹ = sqrt x := by rw [sqrt_eq_rpow, one_div]
  have hbase := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [hhalf, ← one_div, ← one_div] at hbase
  linarith [hpsi (sqrt_nonneg x), hpsi (rpow_nonneg hx0 (1 / 3)),
    hpsi (rpow_nonneg hx0 (1 / 5)), sqrt_nonneg x]

private theorem prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra missing
  have same : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ := by
    ext p
    simp only [Nat.mem_primesLE]
    rw [Nat.le_floor_iff hx, Nat.le_floor_iff (hx.trans hxy)]
    constructor
    · exact fun hp => ⟨hp.1.trans hxy, hp.2⟩
    · intro hp
      exact ⟨le_of_not_gt (fun hpx => missing ⟨p, hp.2, hpx, hp.1⟩), hp.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, same] at h
  exact (lt_irrefl _ h)

/-- A uniform 29 ppm bound for psi supplies the required strict interval above the join. -/
theorem prime_interval_of_psi_error
    (estimate : ∀ x : ℝ, 400000000000000 ≤ x →
      |Chebyshev.psi x - x| ≤ (29 / 1000000 : ℝ) * x)
    {x : ℝ} (hx : 400000000000000 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ 16597 * (p : ℝ) < 16598 * x := by
  let y : ℝ := (16619 / 16618) * x
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hy := hx.trans hxy
  have hcorrection : Chebyshev.psi y - Chebyshev.theta y ≤ (1 / 1000000 : ℝ) * y := by
    have hs := sqrt_scale hy
    linarith [psi_sub_theta_le hy, sqrt_nonneg y]
  have hupper := (abs_le.mp (estimate x hx)).2
  have hlower := (abs_le.mp (estimate y hy)).1
  have htheta : Chebyshev.theta x < Chebyshev.theta y := by
    have gap : (1 + (29 / 1000000 : ℝ)) * x < (1 - (30 / 1000000 : ℝ)) * y := by
      dsimp [y]
      linarith
    linarith [Chebyshev.theta_le_psi x]
  obtain ⟨p, hp, hpx, hpy⟩ := prime_of_theta_lt (by linarith : 0 ≤ x) hxy htheta
  dsimp [y] at hpy
  exact ⟨p, hp, hpx, by linarith⟩

/-- The remaining analytic obligation is the displayed sixfold error estimate. -/
theorem prime_interval_of_smoothed_bound
    (estimate : ∀ x : ℝ, 400000000000000 ≤ x →
      |Chebyshev.psi x - x| ≤
        sqrt x * lowWeight + (x + 1) * highWeight + 1 + log (2 * π) + 3 * step * x)
    {x : ℝ} (hx : 400000000000000 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ 16597 * (p : ℝ) < 16598 * x :=
  prime_interval_of_psi_error (fun t ht => (estimate t ht).trans (budget_le ht)) hx

end ShortPrimeInterval.SexticTail
