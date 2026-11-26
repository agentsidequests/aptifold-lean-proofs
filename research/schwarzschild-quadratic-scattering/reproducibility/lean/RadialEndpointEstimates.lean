import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith

/-! Basic tail and integrability estimates for exterior source terms. -/
namespace SchwarzschildLaurent.Exterior

open Polynomial Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem polynomial_scaled_limit (p : ℂ[X]) (d : ℕ) (degree : p.natDegree ≤ d) :
    Tendsto (fun r : ℝ => p.eval (r : ℂ)/(r : ℂ)^d) atTop (𝓝 (p.coeff d)) := by
  have inv : Tendsto (fun r : ℝ => ((r : ℂ)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [Function.comp_def,Complex.ofReal_zero,Complex.ofReal_inv] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp h)
  have polynomial := ((reflect d p).continuousAt (a := (0 : ℂ))).tendsto.comp inv
  rw [← coeff_zero_eq_eval_zero,coeff_reflect,revAt_zero] at polynomial
  apply polynomial.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r positive
  have r0 : (r : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  let _ := invertibleOfNonzero r0
  have eq := eval₂_reflect_mul_pow (RingHom.id ℂ) (r : ℂ) d p degree
  rw [eval₂_id,eval₂_id,invOf_eq_inv] at eq
  exact (eq_div_iff (pow_ne_zero _ r0)).mpr eq

theorem polynomial_quotient_scaled_limit (p q : ℂ[X]) (d gap : ℕ)
    (degree : p.natDegree ≤ d) (qDegree : q.natDegree = d+gap) (hq : q ≠ 0) :
    Tendsto (fun r : ℝ => (r : ℂ)^gap*(p.eval (r : ℂ)/q.eval (r : ℂ)))
      atTop (𝓝 (p.coeff d/q.leadingCoeff)) := by
  have leading : q.coeff (d+gap) ≠ 0 := by
    rw [← qDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq
  have limits := (polynomial_scaled_limit p d degree).div
    (polynomial_scaled_limit q (d+gap) qDegree.le) leading
  rw [← qDegree,coeff_natDegree] at limits
  apply limits.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r positive
  have r0 : (r : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  change (p.eval (r : ℂ)/(r : ℂ)^d)/(q.eval (r : ℂ)/(r : ℂ)^q.natDegree) =
    (r : ℂ)^gap*(p.eval (r : ℂ)/q.eval (r : ℂ))
  rw [qDegree]
  by_cases root : q.eval (r : ℂ) = 0
  · simp [root]
  · field_simp [pow_add,r0,root]; ring

theorem eventually_bounded_norm_of_limit {α : Type*} {l : Filter α} {f : α → ℂ} {a : ℂ}
    (limit : Tendsto f l (𝓝 a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in l, ‖f x‖ ≤ C := by
  refine ⟨‖a‖+1,by positivity,?_⟩
  exact (limit.norm.eventually (Iio_mem_nhds (lt_add_one ‖a‖))).mono fun x hx => hx.le

/-- Boundedness at the horizon and inverse-square decay at infinity
    give absolute integrability in areal radius. -/
theorem integrable_on_exterior_of_endpoint_bounds (f : ℝ → ℂ)
    (continuous : ContinuousOn f (Ioi (2 : ℝ)))
    (horizon : ∃ C : ℝ, ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖f r‖ ≤ C)
    (infinity : ∃ C : ℝ, ∀ᶠ r in atTop, ‖f r‖ ≤ C*r^(-2 : ℝ)) :
    IntegrableOn f (Ioi (2 : ℝ)) := by
  obtain ⟨C,near⟩ := horizon
  obtain ⟨a,apos,ha⟩ := (nhdsGT_basis (2 : ℝ)).eventually_iff.mp near
  obtain ⟨D,far⟩ := infinity
  obtain ⟨B,hB⟩ := eventually_atTop.mp far
  let b := max a B
  have ab : a ≤ b := le_max_left _ _
  have bpos : 0 < b := by linarith
  have leftMeasure : volume (Ioo (2 : ℝ) a) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have leftInt : IntegrableOn f (Ioo (2 : ℝ) a) := by
    apply (integrableOn_const (C := C) leftMeasure).mono'
    · exact (continuous.mono fun _ h => h.1).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact ha hr
  have middle : IntegrableOn f (Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuous.mono fun _ h => lt_of_lt_of_le apos h.1
  have rightWeight : IntegrableOn (fun r : ℝ => D*r^(-2 : ℝ)) (Ioi b) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) bpos).const_mul D
  have rightInt : IntegrableOn f (Ioi b) := by
    apply rightWeight.mono'
    · exact (continuous.mono fun r hr => lt_trans (lt_of_lt_of_le apos ab) hr).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hB r ((le_max_right a B).trans hr.le)
  have cover : Ioo (2 : ℝ) a ∪ Icc a b ∪ Ioi b = Ioi 2 := by
    ext r
    simp only [mem_union,mem_Ioo,mem_Icc,mem_Ioi]
    constructor
    · rintro ((h | h) | h)
      · exact h.1
      · exact apos.trans_le h.1
      · exact (apos.trans_le ab).trans h
    · intro hr
      by_cases lo : r < a
      · exact .inl (.inl ⟨hr,lo⟩)
      by_cases hi : r ≤ b
      · exact .inl (.inr ⟨le_of_not_gt lo,hi⟩)
      · exact .inr (lt_of_not_ge hi)
  rw [← cover]
  exact (leftInt.union middle).union rightInt

#print axioms polynomial_scaled_limit
#print axioms polynomial_quotient_scaled_limit
#print axioms integrable_on_exterior_of_endpoint_bounds

end
end SchwarzschildLaurent.Exterior
