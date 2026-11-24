import SexticLowZeros
import RSBounds.BacklundCountEndpoint
import Zeta23.ZetaReflect

/-!
# The sixfold low-zero bound for the full finite zeta-zero set

RSBounds supplies the inclusive positive zero set. This bridge checks
the conjugate pairs and leaves the two published weight estimates explicit.
-/

namespace ShortPrimeInterval.SexticTail.LowZeros

open Filter
open scoped BigOperators ComplexConjugate Topology
open TernaryGoldbach.Explicit
open TernaryGoldbach.RSBounds
open TernaryGoldbach.RSBounds.BacklundCountIdentity

private theorem height_pos : 0 < height := by norm_num [height]

theorem closed_head :
    (closedPositiveZeros height).filter (fun ρ => ρ.im ≤ 100) = closedPositiveZeros 100 := by
  classical
  ext ρ
  simp only [Finset.mem_filter, mem_closedPositiveZeros_iff height_pos,
    mem_closedPositiveZeros_iff (by norm_num : (0 : ℝ) < 100)]
  constructor
  · rintro ⟨⟨hz, hi, _⟩, h100⟩
    exact ⟨hz, hi, h100⟩
  · rintro ⟨hz, hi, h100⟩
    exact ⟨⟨hz, hi, h100.trans (by norm_num [height])⟩, h100⟩

private theorem ne_one_of_nonreal {ρ : ℂ} (hρ : ρ.im ≠ 0) : ρ ≠ 1 := by
  intro h
  exact hρ (by simp [h])

noncomputable def lowZeros : Finset ℂ := by
  classical
  exact closedPositiveZeros height ∪ (closedPositiveZeros height).image (starRingEnd ℂ)

/-- Low zeros have nonzero ordinate, including both boundary ordinates. -/
theorem mem_lowZeros {ρ : ℂ} :
    ρ ∈ lowZeros ↔ riemannZeta ρ = 0 ∧ 0 < |ρ.im| ∧ |ρ.im| ≤ height := by
  classical
  simp only [lowZeros, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hp | ⟨σ, hs, rfl⟩)
    · obtain ⟨hz, hi, hH⟩ := (mem_closedPositiveZeros_iff height_pos).mp hp
      simpa only [abs_of_pos hi] using And.intro hz (And.intro hi hH)
    · obtain ⟨hz, hi, hH⟩ := (mem_closedPositiveZeros_iff height_pos).mp hs
      have hconj := Zeta23.riemannZeta_conj (ne_one_of_nonreal hi.ne')
      rw [hz, map_zero] at hconj
      simpa only [Complex.conj_im, abs_neg, abs_of_pos hi] using
        And.intro hconj (And.intro hi hH)
  · rintro ⟨hz, hi, hH⟩
    by_cases hp : 0 < ρ.im
    · left
      apply (mem_closedPositiveZeros_iff height_pos).mpr
      exact ⟨hz, hp, by simpa only [abs_of_pos hp] using hH⟩
    · right
      have hn : ρ.im < 0 := lt_of_le_of_ne (le_of_not_gt hp) (abs_pos.mp hi)
      have hconj := Zeta23.riemannZeta_conj (ne_one_of_nonreal hn.ne)
      rw [hz, map_zero] at hconj
      refine ⟨conj ρ, (mem_closedPositiveZeros_iff height_pos).mpr ?_, by simp⟩
      exact ⟨hconj, by simpa only [Complex.conj_im, neg_pos] using hn,
        by simpa only [Complex.conj_im, abs_of_neg hn] using hH⟩

theorem fullSum_eq_paired (lower : Bool) (x : ℝ) :
    (∑ ρ ∈ lowZeros, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * coefficient lower x ρ) =
      pairedContribution (closedPositiveZeros height) lower x := by
  classical
  have hdisjoint : Disjoint (closedPositiveZeros height)
      ((closedPositiveZeros height).image (starRingEnd ℂ)) := by
    apply Finset.disjoint_left.mpr
    intro ρ hp hn
    obtain ⟨σ, hs, rfl⟩ := Finset.mem_image.mp hn
    have hp_im := ((mem_closedPositiveZeros_iff height_pos).mp hp).2.1
    have hs_im := ((mem_closedPositiveZeros_iff height_pos).mp hs).2.1
    simp only [Complex.conj_im, neg_pos] at hp_im
    exact hp_im.not_gt hs_im
  rw [lowZeros, Finset.sum_union hdisjoint, Finset.sum_image]
  · rw [pairedContribution, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hi := ((mem_closedPositiveZeros_iff height_pos).mp hρ).2.1
    rw [Zeta23.analyticOrderAt_zeta_conj (ne_one_of_nonreal hi.ne'), mul_add]
  · intro a _ b _ h
    simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) h

/-- The sixfold error bound from a bound on the total reciprocal weight. -/
theorem norm_lowZeroSum_le_of_scaled_mass (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hRH : FiniteRH height)
    (hmass : 2 * (1 + 3 * step) * positiveReciprocalMass (closedPositiveZeros height) ≤ 30) :
    ‖∑ ρ ∈ lowZeros, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * coefficient lower x ρ‖ ≤
      30 * Real.sqrt x := by
  rw [fullSum_eq_paired]
  apply norm_pairedContribution_le_of_scaled_mass (closedPositiveZeros height) lower hx hRH _ hmass
  intro ρ hρ
  obtain ⟨hz, hi, hH⟩ := (mem_closedPositiveZeros_iff height_pos).mp hρ
  obtain ⟨hre0, hre1⟩ := xiF_zero_re_strip (xiF_eq_zero_of_zeta_zero hi.ne' hz)
  exact ⟨hz, hre0, hre1, hi, hH⟩

theorem norm_lowZeroSum_le_of_weights (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hRH : FiniteRH height)
    (hhead : positiveReciprocalMass (closedPositiveZeros 100) ≤ 0.592316)
    (htail : tailOrdinateMass (closedPositiveZeros height) ≤ reciprocalTailAllowance) :
    ‖∑ ρ ∈ lowZeros, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * coefficient lower x ρ‖ ≤
      30 * Real.sqrt x := by
  apply norm_lowZeroSum_le_of_scaled_mass lower hx hRH
  apply le_trans (scaledReciprocalMass_le (closedPositiveZeros height) (by rwa [closed_head]) htail)
  exact lowWeight_le

/-- Every rectangle strictly taller than the cutoff contains exactly the same low zeros. -/
theorem filter_rect_eq_lowZeros {T : ℝ} (hT : height < T) :
    (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ height) = lowZeros := by
  classical
  ext ρ
  rw [Finset.mem_filter, mem_lowZeros]
  constructor
  · rintro ⟨hρ, hH⟩
    obtain ⟨hz, hstrip⟩ := zerosRectD_zetaF_cases hρ
    rcases hstrip with hρ0 | ⟨hre0, hre1⟩
    · subst ρ
      rw [zetaF_of_ne (by norm_num), riemannZeta_zero] at hz
      norm_num at hz
    · have hne : ρ ≠ 1 := fun heq => by simp [heq] at hre1
      rw [zetaF_of_ne hne] at hz
      have hzeta := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
      have hξ := (xiF_eq_zero_iff hre0 hre1).mpr hzeta
      exact ⟨hzeta, abs_pos.mpr (xiF_zero_im_ne_zero hξ), hH⟩
  · rintro ⟨hz, hi, hH⟩
    have hi0 := abs_pos.mp hi
    have hre := xiF_zero_re_strip (xiF_eq_zero_of_zeta_zero hi0 hz)
    have hne := ne_one_of_nonreal hi0
    have hTL := hH.trans_lt hT
    have hnorm : ‖ρ - 2‖ < RT T / 2 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
      norm_num only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
      rw [abs_of_neg (by linarith [hre.2] : ρ.re - 2 < 0)]
      unfold RT
      linarith [hre.1]
    have hzetaF : zetaF ρ = 0 := by rw [zetaF_of_ne hne, hz, mul_zero]
    have hmem := mem_zerosIn_of_zeroD ldatum_zeta2 (R := RT T) (r := RT T / 2) (c := 2)
      (by unfold RT; linarith [height_pos]) hnorm hzetaF
    rw [zerosRectD, Finset.mem_filter, zT_re, wT_re, zT_im, wT_im]
    exact ⟨⟨hmem, by linarith [hre.1], by linarith [hre.2],
      (abs_lt.mp hTL).1, (abs_lt.mp hTL).2⟩, hH⟩

private theorem mult_rect_eq_zeta {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ zerosRectD zetaF T) (hne : ρ ≠ 1) :
    multRectD zetaF T ρ = (analyticOrderAt riemannZeta ρ).toNat := by
  have hball : ρ ∈ Metric.closedBall (2 : ℂ) (RT T) := by
    have hnorm := (mem_zerosIn (Finset.mem_filter.mp hρ).1).1
    rw [Metric.mem_closedBall, dist_eq_norm]
    unfold RT at *
    linarith
  have hloc : zetaF =ᶠ[𝓝 ρ] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hne] with s hs
    exact zetaF_of_ne hs
  have hfactor : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := analyticAt_id.sub analyticAt_const
  have horder : analyticOrderAt zetaF ρ = analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_congr hloc,
      show (fun s => (s - 1) * riemannZeta s) = (fun s => s - 1) * riemannZeta from rfl,
      analyticOrderAt_mul hfactor (analyticOn_riemannZeta ρ hne),
      hfactor.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hne), zero_add]
  rw [multRectD, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => differentiable_zetaF.analyticAt z : AnalyticOnNhd ℂ zetaF
      (Metric.closedBall 2 (RT T))) hball, horder]
  cases analyticOrderAt riemannZeta ρ <;> simp

/-- The low portion of each finite contour uses the same exact zero sum. -/
theorem rect_lowZeroSum_eq (lower : Bool) (x : ℝ) {T : ℝ} (hT : height < T) :
    (∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ height),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ) =
    ∑ ρ ∈ lowZeros, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * coefficient lower x ρ := by
  classical
  rw [filter_rect_eq_lowZeros hT]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hi := (mem_lowZeros.mp hρ).2.1
  have hf : ρ ∈ (zerosRectD zetaF T).filter (fun u => |u.im| ≤ height) := by
    rwa [filter_rect_eq_lowZeros hT]
  have hmem := (Finset.mem_filter.mp hf).1
  rw [mult_rect_eq_zeta (height_pos.trans hT) hmem (ne_one_of_nonreal (abs_pos.mp hi))]

theorem norm_rect_lowZeroSum_le_of_weights (lower : Bool) {x T : ℝ} (hx : 0 < x)
    (hT : height < T) (hRH : FiniteRH height)
    (hhead : positiveReciprocalMass (closedPositiveZeros 100) ≤ 0.592316)
    (htail : tailOrdinateMass (closedPositiveZeros height) ≤ reciprocalTailAllowance) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ height),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤ 30 * Real.sqrt x := by
  rw [rect_lowZeroSum_eq lower x hT]
  exact norm_lowZeroSum_le_of_weights lower hx hRH hhead htail

end ShortPrimeInterval.SexticTail.LowZeros
