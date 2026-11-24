import SexticLowZerosActual
import RSBounds.BacklundHighCount
import RSBounds.BacklundLowMainTerm
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# A bound for the low reciprocal weights without enumerating the zeros

At 1 the real part of the xi logarithmic derivative bounds the inverse
square weights of conjugate critical-line zeros. The count at 100 then
turns this into a bound on the inverse first powers.
-/

namespace ShortPrimeInterval.SexticTail.LowZeros

open Complex Filter
open scoped BigOperators ComplexConjugate Topology
open TernaryGoldbach.Explicit
open TernaryGoldbach.RSBounds
open TernaryGoldbach.RSBounds.BacklundCountIdentity

private theorem log_three_ge : (109 / 100 : ℝ) ≤ Real.log 3 := by
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 109
  have he : Real.exp 1 ^ 109 ≤ (3 : ℝ) ^ 100 := h.trans (by norm_num)
  have hl := Real.log_le_log (by positivity : 0 < Real.exp 1 ^ 109) he
  rw [Real.log_pow, Real.log_exp, Real.log_pow] at hl
  norm_num at hl
  linarith

private theorem logDeriv_xi_at_one :
    logDeriv xiF 1 = 1 - Complex.log (Real.pi : ℂ) / 2 - Complex.log 2 +
      (Real.eulerMascheroniConstant : ℂ) / 2 := by
  have hloc : xiF =ᶠ[𝓝 (1 : ℂ)] fun s => s * Gammaℝ s * riemannZeta₁ s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 0 < (1 : ℂ).re by norm_num)] with s hs
    by_cases hne : s = 1
    · subst s
      simp [xiF_one, Gammaℝ_one]
    · rw [xiF_eq hs hne, zetaF_of_ne hne, riemannZeta_eq_inv_sub_mul hne]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]
  have hΓ : DifferentiableAt ℂ Gammaℝ 1 :=
    (Complex.analyticAt_Gammaℝ (by norm_num : 0 < (1 : ℂ).re)).differentiableAt
  have hG0 : Gammaℝ (1 : ℂ) ≠ 0 := by simp [Gammaℝ_one]
  have hZ : DifferentiableAt ℂ riemannZeta₁ 1 := differentiable_riemannZeta₁ 1
  have hZ0 : riemannZeta₁ (1 : ℂ) ≠ 0 := by simp
  rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
    logDeriv_mul (f := fun s : ℂ => s * Gammaℝ s) (g := riemannZeta₁) 1
      (mul_ne_zero one_ne_zero hG0) hZ0 (differentiableAt_id.mul hΓ) hZ,
    logDeriv_mul (f := fun s : ℂ => s) (g := Gammaℝ) 1 one_ne_zero hG0 differentiableAt_id hΓ,
    logDeriv_id', logDeriv_Gammaℝ (by norm_num : 0 < (1 : ℂ).re),
    digamma_one_half, logDeriv_apply, deriv_riemannZeta₁_one, riemannZeta₁_one]
  ring

private theorem logDeriv_xi_re_le : (logDeriv xiF 1).re ≤ 1 / 10 := by
  have hp := log_three_ge.trans (Real.log_le_log (by norm_num) Real.pi_gt_three.le)
  have h2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (x := 2) zero_le_two).symm
  rw [logDeriv_xi_at_one, ← Complex.ofReal_log Real.pi_pos.le, h2]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.ofReal_re]
  linarith [Real.log_two_gt_d9, Real.eulerMascheroniConstant_lt_two_thirds]

private noncomputable def momentTerm (ρ : ℂ) : ℝ :=
  ((analyticOrderAt xiF ρ).toNat : ℝ) * ((1 - ρ)⁻¹).re

private theorem momentTerm_nonneg {ρ : ℂ} (hz : xiF ρ = 0) : 0 ≤ momentTerm ρ := by
  have hre := (xiF_zero_re_strip hz).2
  unfold momentTerm
  rw [Complex.inv_re, Complex.sub_re, Complex.one_re]
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (Complex.normSq_nonneg _))

private theorem sq_multiplicity {T : ℝ} (hT : 0 < T) {ρ : ℂ} (hρ : ρ ∈ sqZeros T) :
    mult T ρ = (analyticOrderAt xiF ρ).toNat := by
  have hr := (mem_sqZeros_iff hρ).2.1
  have hi := (mem_sqZeros_iff hρ).2.2
  have hball : ρ ∈ Metric.closedBall (1 / 2 : ℂ) (6 * T) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    norm_num only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, zero_div, sub_zero]
    linarith
  rw [mult, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun s _ => differentiable_xiF.analyticAt s : AnalyticOnNhd ℂ xiF
      (Metric.closedBall (1 / 2) (6 * T))) hball]
  cases analyticOrderAt xiF ρ <;> simp

private theorem xi_moment_bound (zeros : Finset ℂ) (hzero : ∀ ρ ∈ zeros, xiF ρ = 0) :
    (∑ ρ ∈ zeros, momentTerm ρ) ≤ (logDeriv xiF 1).re := by
  classical
  let M : ℝ := (∑ ρ ∈ zeros, ‖ρ - 1 / 2‖) + 1
  have hM : 1 ≤ M := by
    unfold M
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun ρ _ => norm_nonneg (ρ - 1 / 2)))
  have hm (ρ : ℂ) (hρ : ρ ∈ zeros) : ‖ρ - 1 / 2‖ ≤ M := by
    have hh := Finset.single_le_sum (f := fun u : ℂ => ‖u - 1 / 2‖)
      (fun u _ => norm_nonneg (u - 1 / 2)) hρ
    unfold M
    linarith
  by_contra h
  have hstrict := lt_of_not_ge h
  let ε := ((∑ ρ ∈ zeros, momentTerm ρ) - (logDeriv xiF 1).re) / 2
  have hε : 0 < ε := by unfold ε; linarith
  obtain ⟨T, ht, happrox, hinclude, hall⟩ := xi_partial_approx (by linarith : 0 ≤ M) hε
  have hsub : zeros ⊆ sqZeros T := fun ρ hρ => (hinclude ρ (hzero ρ hρ) (hm ρ hρ)).1
  have hmagnitude : ‖(1 : ℂ) - 1 / 2‖ ≤ M := by
    rw [show (1 : ℂ) - 1 / 2 = (1 / 2 : ℝ) by norm_num, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    linarith
  have hξ : xiF (1 : ℂ) ≠ 0 := by rw [xiF_one]; exact one_ne_zero
  have hb := happrox 1 hmagnitude hξ
  let S : ℂ := ∑ ρ ∈ sqZeros T, (mult T ρ : ℂ) * ((1 : ℂ) - ρ)⁻¹
  have heq : logDeriv xiF 1 - S =
      logDeriv xiF 1 + ∑ ρ ∈ sqZeros T, (mult T ρ : ℂ) * (ρ - 1)⁻¹ := by
    unfold S
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ρ _
    rw [← mul_neg, ← inv_neg, neg_sub]
  rw [← heq] at hb
  have hreal := (Complex.abs_re_le_norm (logDeriv xiF 1 - S)).trans hb
  have hs : S.re = ∑ ρ ∈ sqZeros T, momentTerm ρ := by
    unfold S
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [momentTerm, sq_multiplicity ht hρ, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
  rw [Complex.sub_re, hs] at hreal
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ρ hρ _ => momentTerm_nonneg (hall ρ hρ))
  unfold ε at hreal
  linarith only [(abs_le.mp hreal).1, hle, hstrict]

private theorem re_inverse_at_line {ρ : ℂ} (h : ρ.re = 1 / 2) :
    ((1 - ρ)⁻¹).re = 1 / (2 * ‖ρ‖ ^ 2) := by
  have hs : Complex.normSq (1 - ρ) = ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, zero_sub, h]
    ring
  rw [Complex.inv_re, hs, Complex.sub_re, Complex.one_re, h]
  ring

private theorem height_pos100 : (0 : ℝ) < 100 := by norm_num

private theorem head_square_mass_le (hRH : FiniteRH height) :
    (∑ ρ ∈ closedPositiveZeros 100, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖ ^ 2) ≤ 1 / 10 := by
  classical
  let head := closedPositiveZeros 100
  let reflected := head.image (starRingEnd ℂ)
  have hpos (ρ : ℂ) (hρ : ρ ∈ head) := (mem_closedPositiveZeros_iff height_pos100).mp hρ
  have hdis : Disjoint head reflected := by
    apply Finset.disjoint_left.mpr
    intro ρ hρ hr
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hr
    have hi := (hpos _ hρ).2.1
    rw [Complex.conj_im] at hi
    linarith [(hpos _ hσ).2.1]
  have hξ (ρ : ℂ) (hρ : ρ ∈ head) : xiF ρ = 0 :=
    xiF_eq_zero_of_zeta_zero (hpos ρ hρ).2.1.ne' (hpos ρ hρ).1
  have hz (ρ : ℂ) (hρ : ρ ∈ head ∪ reflected) : xiF ρ = 0 := by
    rcases Finset.mem_union.mp hρ with hp | hn
    · exact hξ _ hp
    · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hn
      rw [xiF_conj, hξ _ hσ, map_zero]
  have hmoment := xi_moment_bound (head ∪ reflected) hz
  rw [Finset.sum_union hdis, show reflected = head.image (starRingEnd ℂ) from rfl,
    Finset.sum_image] at hmoment
  · rw [← Finset.sum_add_distrib] at hmoment
    apply le_trans _ (hmoment.trans logDeriv_xi_re_le)
    apply Finset.sum_le_sum
    intro ρ hρ
    have hstrip := xiF_zero_re_strip (hξ _ hρ)
    obtain ⟨hp, hi, hB⟩ := hpos ρ hρ
    have hline := hRH ρ hp hstrip.1 hstrip.2
      (by rw [abs_of_pos hi]; exact hB.trans (by norm_num [height]))
    have hline' : (conj ρ).re = 1 / 2 := by simpa only [Complex.conj_re] using hline
    have hne : ρ ≠ 1 := by intro he; simp [he] at hi
    have hξ' : xiF (conj ρ) = 0 := by rw [xiF_conj, hξ _ hρ, map_zero]
    unfold momentTerm
    rw [analyticOrderAt_xi_eq_zeta (hξ _ hρ), analyticOrderAt_xi_eq_zeta hξ',
      Zeta23.analyticOrderAt_zeta_conj hne, re_inverse_at_line hline, re_inverse_at_line hline',
      Complex.norm_conj]
    apply le_of_eq
    ring
  · intro u _ v _ huv
    simpa [Complex.conj_conj] using congrArg (starRingEnd ℂ) huv

theorem rosserR_hundred_le : rosserR 1.588 100 ≤ 4 := by
  have hL : Real.log 100 < 5 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num : 0 < (100 : ℝ))).2
    have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : 5 ≠ 0)
    rw [← Real.exp_nat_mul] at h
    simp only [Nat.cast_ofNat, mul_one] at h
    exact (by norm_num : (100 : ℝ) < 2.7182818283 ^ 5).trans h
  have hr : Real.log (Real.log 100) ≤ 2 := by
    apply (Real.log_le_iff_le_exp (Real.log_pos (by norm_num))).2
    have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : 2 ≠ 0)
    rw [← Real.exp_nat_mul] at h
    simp only [Nat.cast_ofNat, mul_one] at h
    exact hL.le.trans ((by norm_num : (5 : ℝ) ≤ 2.7182818283 ^ 2).trans h.le)
  unfold rosserR
  linarith

private theorem count_head_le : (N_le 100 : ℝ) ≤ 34 := by
  have hf := BacklundLowScalar.rosserF_hundred_lt
  have hn := (abs_lt.mp (rosser_bound_high (T := 100) le_rfl)).2
  change (N_le 100 : ℝ) - rosserF 100 < rosserR 1.588 100 at hn
  have herr := rosserR_hundred_le
  linarith

/-- A coarser head bound that uses only the analytic count and the xi moment. -/
theorem positiveReciprocalMass_head_le_from_moment (hRH : FiniteRH height) :
    positiveReciprocalMass (closedPositiveZeros 100) ≤ 1.85 := by
  have hsq := head_square_mass_le hRH
  have hcount : (∑ ρ ∈ closedPositiveZeros 100, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) ≤ 34 := by
    simpa [N_le] using count_head_le
  calc
    _ ≤ ∑ ρ ∈ closedPositiveZeros 100, (10 * (((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖ ^ 2) +
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / 40) := by
        unfold positiveReciprocalMass
        apply Finset.sum_le_sum
        intro ρ _
        have h := sq_nonneg (‖ρ‖⁻¹ - 1 / 20)
        have hh : ‖ρ‖⁻¹ ≤ 10 * (‖ρ‖ ^ 2)⁻¹ + 1 / 40 := by
          rw [← inv_pow]
          nlinarith only [h]
        have he := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg ((analyticOrderAt riemannZeta ρ).toNat))
        simp only [div_eq_mul_inv] at he ⊢
        linarith only [he]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      linarith only [hsq, hcount]

end ShortPrimeInterval.SexticTail.LowZeros
