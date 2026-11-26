import HorizonSeedEstimates
import LinearExteriorWave
import Mathlib.Analysis.Analytic.Uniqueness

/-! The whole convergent horizon collar agrees with the globally continued
wave. The radius is explicit and can be kept fixed as the frequency tends to zero. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set
open scoped Topology NNReal
open SchwarzschildLaurent.Horizon
open SchwarzschildLaurent.Outgoing (RadialEquation radiusLapse rwPotential exterior_lapse_nonzero)
open SchwarzschildMixtures.Strain

noncomputable section

theorem horizon_envelope_solves_on_ball (k L : ℂ) (ki : k.re = 0) {R : ℝ≥0}
    (rp : 0 < R) (bound : horizonGrowth k L*(R:ℝ) ≤ 1) :
    EqOn (Horizon.horizonResidual k L (ingoingEnvelope k L)) 0 (Metric.ball 0 (R:ℝ)) := by
  let H := ingoingEnvelope k L
  have series := ingoing_power_series_on_ball k L ki rp bound
  have analytic : AnalyticOnNhd ℂ H (Metric.ball 0 (R:ℝ)) := by
    simpa only [Metric.eball_coe] using series.analyticOnNhd
  have residual : AnalyticOnNhd ℂ (Horizon.horizonResidual k L H) (Metric.ball 0 (R:ℝ)) := by
    intro z hz
    have h := analytic z hz
    have hd := h.deriv
    have hdd := hd.deriv
    unfold Horizon.horizonResidual
    fun_prop
  have zeroInside : (0:ℂ) ∈ Metric.ball 0 (R:ℝ) := Metric.mem_ball_self (by exact_mod_cast rp)
  exact residual.eqOn_of_preconnected_of_eventuallyEq
    (fun _ _ => analyticAt_const)
    (convex_ball (0:ℂ) (R:ℝ)).isPreconnected zeroInside (ingoing_envelope_equation k L ki)

/-- Matching at any radius strictly inside the certified horizon series. -/
theorem ingoing_wave_matches_collar (k L : ℂ) (ki : k.re = 0) {R : ℝ≥0}
    (rp : 0 < R) (bound : horizonGrowth k L*(R:ℝ) ≤ 1)
    (u du : ℝ → ℂ) (equation : RadialEquation radiusLapse (rwPotential k L) 0 u du)
    (atHorizon : u =ᶠ[𝓝[>] (2:ℝ)] horizonBranch k L 1)
    {r : ℝ} (r2 : 2 < r) (inside : r-2 < (R:ℝ)) :
    (u r,du r) = ingoingTrajectory k (normalizedEnvelope k L) r := by
  let H := normalizedEnvelope k L
  let J := ingoingTrajectory k H
  let U := fun s : ℝ => (u s,du s)
  have series := ingoing_power_series_on_ball k L ki rp bound
  have residual := horizon_envelope_solves_on_ball k L ki rp bound
  have shiftDeriv : deriv H = fun z => deriv (ingoingEnvelope k L) (z-2) := by
    funext z
    exact deriv_comp_sub_const _ _ _
  have localODE (s : ℝ) (hs : 2 < s) (sr : s ≤ r) :
      HasDerivAt J (exteriorSystem k L s (J s)) s := by
    have close : (s:ℂ)-2 ∈ Metric.ball 0 (R:ℝ) := by
      rw [Metric.mem_ball,dist_eq_norm,sub_zero,← Complex.ofReal_ofNat,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hs)]
      exact (sub_le_sub_right sr _).trans_lt inside
    have a := series.analyticOnNhd ((s:ℂ)-2) (by simpa only [Metric.eball_coe] using close)
    have aa : AnalyticAt ℂ H (s:ℂ) :=
      a.comp (f := fun z : ℂ => z-2) (by fun_prop)
    have law : arealHorizonResidual k L H (s:ℂ) = 0 := by
      simpa only [arealHorizonResidual,shiftDeriv,H,normalizedEnvelope,deriv_comp_sub_const,
        Horizon.horizonResidual,sub_add_cancel,Pi.zero_apply] using residual close
    exact ingoing_trajectory_equation_at k L H hs aa law
  obtain ⟨b,hb,matchValue⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 atHorizon
  let a : ℝ := (2+min r b)/2
  have min2 : 2 < min r b := lt_min r2 hb
  have a2 : 2 < a := by dsimp only [a]; linarith
  have am : a < min r b := by dsimp only [a]; linarith
  have ar : a < r := am.trans_le (min_le_left _ _)
  have ab : a < b := am.trans_le (min_le_right _ _)
  have near : u =ᶠ[𝓝 a] fun s => (J s).1 := by
    filter_upwards [Ioo_mem_nhds a2 ab] with s hs
    have e := matchValue hs
    change u s = horizonBranch k L 1 s at e
    have scaleOne : horizonEnvelope k L 1 = H := by funext z; simp [H,horizonEnvelope]
    simpa only [J,ingoingTrajectory,horizonBranch,scaleOne] using e
  have eqA : U a = J a := by
    refine Prod.ext near.eq_of_nhds ?_
    have dj := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt a (localODE a a2 ar.le)
    rw [exterior_system_eq k L a a2] at dj
    have derivative : HasDerivAt (fun s => (J s).1) ((J a).2/radiusLapse a) a := dj
    exact (div_left_inj' (exterior_lapse_nonzero a2)).1
      ((equation.value a a2).unique (derivative.congr_of_eventuallyEq near))
  let F := fun (s : ℝ) => exteriorSystem k L (max s a)
  apply closed_interval_agreement F _ (exterior_clamped_system_lipschitz k L a2)
    U J eqA ar.le (le_refl r) (le_refl r)
  · intro s hs
    have s2 := a2.trans_le hs.1
    have prod := (equation.value s s2).prodMk (equation.jet s s2)
    simpa only [F,max_eq_left hs.1,U,exterior_system_eq k L s s2,Pi.zero_apply,add_zero]
      using prod.hasDerivWithinAt (s := Icc a r)
  · intro s hs
    simpa only [F,max_eq_left hs.1] using
      (localODE s (a2.trans_le hs.1) hs.2).hasDerivWithinAt (s := Icc a r)

#print axioms horizon_envelope_solves_on_ball
#print axioms ingoing_wave_matches_collar

end
end SchwarzschildLaurent.LinearWave
