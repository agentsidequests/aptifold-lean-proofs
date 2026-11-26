import LinearODEContinuation
import LinearScatteringModes
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Continue the convergent horizon series to a homogeneous exterior
Regge–Wheeler wave. The state consists of its value and tortoise jet. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set
open scoped Topology NNReal
open SchwarzschildLaurent.Outgoing SchwarzschildLaurent.Horizon
open SchwarzschildMixtures SchwarzschildMixtures.Strain

noncomputable section

def exteriorWeight (r : ℝ) : ℂ := 1+2/((r : ℂ)-2)

def exteriorSystem (w L : ℂ) (r : ℝ) (y : ℂ × ℂ) : ℂ × ℂ :=
  (y.2*exteriorWeight r,(w^2*exteriorWeight r+tailPotential L r)*y.1)

private theorem exterior_weight_eq (r : ℝ) (hr : 2 < r) : exteriorWeight r = (radiusLapse r)⁻¹ := by
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  have gap : (r : ℂ)-2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hr.ne')
  simp only [exteriorWeight,radiusLapse,inv_div]
  field_simp [nz,gap]
  ring

theorem exterior_system_eq (w L : ℂ) (r : ℝ) (hr : 2 < r) (y : ℂ × ℂ) :
    exteriorSystem w L r y =
      (y.2/radiusLapse r,rwPotential w L r*y.1/radiusLapse r) := by
  unfold exteriorSystem
  rw [exterior_weight_eq r hr]
  refine Prod.ext rfl ?_
  change _ = (w^2+radiusLapse r*tailPotential L r)*y.1/radiusLapse r
  field_simp [exterior_lapse_nonzero hr]

private theorem exterior_continuous (w L : ℂ) (y : ℂ × ℂ) :
    ContinuousOn (fun r => exteriorSystem w L r y) (Ioi 2) := by
  have realCast : ContinuousOn (fun r : ℝ => (r : ℂ)) (Ioi 2) := Complex.continuous_ofReal.continuousOn
  have radius0 : ∀ r : ℝ, r ∈ Ioi 2 → (r : ℂ) ≠ 0 := fun r hr => by
    exact_mod_cast (show r ≠ 0 by linarith [show 2 < r from hr])
  have gap0 : ∀ r : ℝ, r ∈ Ioi 2 → (r : ℂ)-2 ≠ 0 := fun r hr => by
    exact sub_ne_zero.2 (by exact_mod_cast (show 2 < r from hr).ne')
  have W : ContinuousOn exteriorWeight (Ioi 2) := by
    unfold exteriorWeight
    exact continuousOn_const.add (continuousOn_const.div (realCast.sub continuousOn_const) gap0)
  have tail : ContinuousOn (tailPotential L) (Ioi 2) := by
    unfold tailPotential
    exact (continuousOn_const.div (realCast.pow 2) (fun r h => pow_ne_zero _ (radius0 r h))).sub
      (continuousOn_const.div (realCast.pow 3) (fun r h => pow_ne_zero _ (radius0 r h)))
  exact (continuousOn_const.mul W).prodMk
    (((continuousOn_const.mul W).add tail).mul continuousOn_const)

private def systemCap (w L : ℂ) (a : ℝ) : ℝ :=
  (‖w‖^2+1)*(1+2/(a-2))+(‖L‖+3)

private theorem system_cap_nonnegative (w L : ℂ) {a : ℝ} (ha : 2 < a) : 0 ≤ systemCap w L a := by
  have ap : 0 < a-2 := sub_pos.2 ha
  unfold systemCap
  positivity

private theorem norm_exterior_weight {a r : ℝ} (a2 : 2 < a) (ar : a ≤ r) :
    ‖exteriorWeight r‖ ≤ 1+2/(a-2) := by
  have rp : 0 < r-2 := by linarith
  have ap : 0 < a-2 := sub_pos.2 a2
  have coh : exteriorWeight r = (↑(1+2/(r-2) : ℝ) : ℂ) := by
    unfold exteriorWeight
    push_cast
    rfl
  rw [coh,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1+2/(r-2))]
  exact add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) ap (by linarith))

private theorem norm_exterior_system (w L : ℂ) {a r : ℝ} (a2 : 2 < a) (ar : a ≤ r)
    (y : ℂ × ℂ) : ‖exteriorSystem w L r y‖ ≤ systemCap w L a*‖y‖ := by
  have ap : 0 < a-2 := sub_pos.2 a2
  have wbound := norm_exterior_weight a2 ar
  have mass : 0 ≤ 1+2/(a-2) := by positivity
  have r2 : 2 < r := a2.trans_le ar
  have long : ‖tailPotential L r‖ ≤ ‖L‖+3 :=
    (norm_tail_potential L r r2).trans (div_le_self (by positivity) (by nlinarith))
  have right : ‖w^2*exteriorWeight r+tailPotential L r‖ ≤ (‖w‖^2)*(1+2/(a-2))+(‖L‖+3) := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_pow]
    exact add_le_add (mul_le_mul_of_nonneg_left wbound (sq_nonneg _)) long
  have boundW : 1+2/(a-2) ≤ systemCap w L a := by
    unfold systemCap
    rw [add_mul,one_mul]
    linarith [mul_nonneg (sq_nonneg ‖w‖) mass, norm_nonneg L]
  have boundR : ‖w‖^2*(1+2/(a-2))+(‖L‖+3) ≤ systemCap w L a := by
    unfold systemCap
    rw [add_mul,one_mul]
    linarith
  simp only [exteriorSystem,Prod.norm_def,norm_mul]
  apply max_le
  · calc
      _ ≤ ‖y‖*systemCap w L a := mul_le_mul (norm_snd_le y) (wbound.trans boundW)
        (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · exact mul_le_mul (right.trans boundR) (norm_fst_le y) (norm_nonneg _)
      (system_cap_nonnegative _ _ a2)

private theorem exterior_sub (w L : ℂ) (r : ℝ) (x y : ℂ × ℂ) :
    exteriorSystem w L r (x-y) = exteriorSystem w L r x - exteriorSystem w L r y := by
  refine Prod.ext ?_ ?_ <;> simp [exteriorSystem,sub_mul,mul_sub]

private theorem complex_carrier_analytic (w : ℂ) {z : ℂ} (h : z/2-1 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (ingoingCarrier w) z := by
  have arg : AnalyticAt ℂ (fun s : ℂ => s/2-1) z := by fun_prop
  have log := arg.clog h
  unfold ingoingCarrier tortoise
  fun_prop

def ingoingTrajectory (w : ℂ) (H : ℂ → ℂ) (r : ℝ) : ℂ × ℂ :=
  let J := ingoingWave w H
  (J (r : ℂ),tortoiseDifferential J (r : ℂ))

theorem ingoing_trajectory_equation_at (w L : ℂ) (H : ℂ → ℂ) {r : ℝ} (r2 : 2 < r)
    (hH : AnalyticAt ℂ H (r:ℂ)) (hEq : arealHorizonResidual w L H (r:ℂ) = 0) :
    HasDerivAt (ingoingTrajectory w H) (exteriorSystem w L r (ingoingTrajectory w H r)) r := by
  let J := ingoingWave w H
  let dJ := tortoiseDifferential J
  let z : ℂ := r
  have nz : z ≠ 0 := by
    change (r : ℂ) ≠ 0
    exact_mod_cast (show r ≠ 0 by linarith)
  have cut := exterior_log_argument r r2
  have f0 := exterior_lapse_nonzero r2
  have wAnal : AnalyticAt ℂ J z := (complex_carrier_analytic w cut).fun_mul hH
  have fAnal : AnalyticAt ℂ radialLapse z := by
    unfold radialLapse
    exact (show AnalyticAt ℂ (fun t : ℂ => t-2) z by fun_prop).fun_div analyticAt_id nz
  have djAnal : AnalyticAt ℂ dJ z := fAnal.fun_mul wAnal.deriv
  have law := ingoing_wave_from_envelope w L cut nz hH hEq
  change radiusLapse r*deriv dJ z = rwPotential w L r*J z at law
  have hv := wAnal.differentiableAt.hasDerivAt.comp_ofReal
  have hd := djAnal.differentiableAt.hasDerivAt.comp_ofReal
  rw [exterior_system_eq w L r r2]
  apply (hv.prodMk hd).congr_deriv
  refine Prod.ext ?_ ?_
  · change deriv J z = (radiusLapse r*deriv J z)/radiusLapse r
    exact (mul_div_cancel_left₀ _ f0).symm
  · change deriv dJ z = rwPotential w L r*J z/radiusLapse r
    apply (eq_div_iff f0).2
    simpa [mul_comm] using law

/-- A single Lipschitz coefficient works on the entire exterior to the right
of a fixed starting radius. Clamping permits the interval uniqueness lemma. -/
theorem exterior_clamped_system_lipschitz (w L : ℂ) {a : ℝ} (ha : 2 < a) :
    ∀ r : ℝ, LipschitzWith (systemCap w L a).toNNReal (exteriorSystem w L (max r a)) := by
  intro r
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,← exterior_sub,Real.coe_toNNReal _ (system_cap_nonnegative _ _ ha)]
  exact norm_exterior_system w L ha (le_max_right r a) _

private abbrev horizonTrajectory (w L a : ℂ) := ingoingTrajectory w (horizonEnvelope w L a)

private theorem horizon_trajectory_equation (w L a : ℂ) (wi : w.re = 0) :
    ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), HasDerivAt (horizonTrajectory w L a)
      (exteriorSystem w L r (horizonTrajectory w L a r)) r := by
  have ah : AnalyticAt ℂ (horizonEnvelope w L a) 2 :=
    (analyticAt_const (v := a)).fun_mul (normalized_envelope_analytic w L wi)
  filter_upwards [self_mem_nhdsWithin,exterior_horizon_radius.eventually ah.eventually_analyticAt,
    exterior_horizon_radius.eventually (scaled_envelope_residual w L a wi)] with r hr hH hEq
  exact ingoing_trajectory_equation_at w L _ hr hH hEq

/-- Every normalization of the convergent ingoing series extends to
a wave and a tortoise jet on the entire Schwarzschild exterior. -/
theorem global_regge_wheeler_wave (w L a : ℂ) (wi : w.re = 0) :
    ∃ u du : ℝ → ℂ, RadialEquation radiusLapse (rwPotential w L) 0 u du ∧
      u =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch w L a := by
  let nearHorizon := horizonTrajectory w L a
  obtain ⟨b,hb,localEq⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (horizon_trajectory_equation w L a wi)
  let start : ℝ := (2+b)/2
  have hs : 2 < start := by dsimp only [start]; linarith [show 2 < b from hb]
  have sb : start < b := by dsimp only [start]; linarith [show 2 < b from hb]
  let F := fun (r : ℝ) => exteriorSystem w L (max r start)
  let K : ℝ≥0 := (systemCap w L start).toNNReal
  have lip : ∀ r, LipschitzWith K (F r) := exterior_clamped_system_lipschitz w L hs
  have fzero : ∀ r, F r 0 = 0 := by intro r; simp [F,exteriorSystem]
  have fc : ∀ y, Continuous (fun r => F r y) := fun y =>
    (exterior_continuous w L y).comp_continuous (continuous_id.max continuous_const)
      (fun r => hs.trans_le (le_max_right r start))
  obtain ⟨right,matchAt,dr⟩ := global_right_trajectory F K lip fzero fc start (nearHorizon start)
  let j := joinAt start nearHorizon right
  have D : ∀ r, 2 < r → HasDerivAt j (exteriorSystem w L r (j r)) r := by
    intro r hr
    apply (joined_derivative (exteriorSystem w L) (Ioi 2) start nearHorizon right matchAt.symm ?_ ?_ r hr).hasDerivAt
      (Ioi_mem_nhds hr)
    · intro s ht
      exact (localEq ⟨ht.1,(show s ≤ start from ht.2).trans_lt sb⟩).hasDerivWithinAt
    · intro s ht
      have d := (dr s ht.2).mono (inter_subset_right : Ioi (2:ℝ) ∩ Ici start ⊆ Ici start)
      simpa only [F,max_eq_left (show start ≤ s from ht.2)] using d
  let u := fun r => (j r).1
  let du := fun r => (j r).2
  refine ⟨u,du,⟨?_,?_⟩,?_⟩
  · intro r hr
    have h := D r hr
    rw [exterior_system_eq w L r hr] at h
    exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h
  · intro r hr
    have h := D r hr
    rw [exterior_system_eq w L r hr] at h
    have jet := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h
    change HasDerivAt du (rwPotential w L r*u r/radiusLapse r) r at jet
    simpa only [Pi.zero_apply,add_zero] using jet
  · filter_upwards [mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨start,hs,subset_rfl⟩] with r hr
    simp only [u,j,joinAt,if_pos (show r ≤ start from hr.2.le),nearHorizon,horizonTrajectory,
      ingoingTrajectory,horizonBranch]

#print axioms exterior_system_eq
#print axioms ingoing_trajectory_equation_at
#print axioms exterior_clamped_system_lipschitz
#print axioms global_regge_wheeler_wave

end
end SchwarzschildLaurent.LinearWave
