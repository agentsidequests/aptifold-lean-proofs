import OutgoingQuadraticLimits
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic

/-! The reciprocally analytic coefficient rows at infinity and the
ingoing analytic envelopes at the future horizon. -/
namespace SchwarzschildLaurent.Outgoing

open Filter Set
open scoped Topology

noncomputable section

def radiusLapse (r : ℝ) : ℂ := ((r : ℂ)-2)/(r : ℂ)

def inverseRadius (r : ℝ) : ℂ := (r : ℂ)⁻¹

def rwPotential (k L : ℂ) (r : ℝ) : ℂ :=
  k^2+radiusLapse r*(L/(r : ℂ)^2-6/(r : ℂ)^3)

theorem exterior_lapse_nonzero {r : ℝ} (hr : 2 < r) : radiusLapse r ≠ 0 := by
  unfold radiusLapse
  apply div_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast hr.ne')
  · exact_mod_cast (show r ≠ 0 by linarith)

theorem inverse_radius_tends_to_zero : Tendsto inverseRadius atTop (𝓝 (0 : ℂ)) := by
  have real := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have coe := (Complex.continuous_ofReal.continuousAt (x := (0:ℝ))).tendsto.comp real
  change Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 (0 : ℂ))
  simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using coe

theorem lapse_tends_to_one : Tendsto radiusLapse atTop (𝓝 (1 : ℂ)) := by
  have lim := (tendsto_const_nhds (x := (1:ℂ))).sub (inverse_radius_tends_to_zero.const_mul 2)
  simp only [mul_zero,sub_zero] at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop (2:ℝ)] with r hr
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  simp only [inverseRadius,radiusLapse,div_eq_mul_inv]
  field_simp [nz]

theorem potential_tends_to_frequency (k L : ℂ) : Tendsto (rwPotential k L) atTop (𝓝 (k^2)) := by
  have u := inverse_radius_tends_to_zero
  have lim := (tendsto_const_nhds (x := k^2)).add
    (lapse_tends_to_one.mul (((u.pow 2).const_mul L).sub ((u.pow 3).const_mul 6)))
  change Tendsto (fun r : ℝ => k^2+radiusLapse r*(L/(r : ℂ)^2-6/(r : ℂ)^3)) atTop (𝓝 (k^2))
  simpa [inverseRadius,inv_pow,div_eq_mul_inv] using lim

def reciprocalValue (A : ℂ → Coefficients) (r : ℝ) : Coefficients := A (inverseRadius r)

private def reciprocalDerivative (A : ℂ → ℂ) (r : ℝ) : ℂ :=
  radiusLapse r*(deriv A (inverseRadius r)*(-(inverseRadius r)^2))

def reciprocalJet (A : ℂ → Coefficients) (r : ℝ) : Coefficients :=
  (reciprocalDerivative (fun z => (A z).1) r,
    reciprocalDerivative (fun z => (A z).2.1) r,
    reciprocalDerivative (fun z => (A z).2.2) r)

private theorem reciprocal_component (A : ℂ → ℂ) (ah : AnalyticAt ℂ A 0) :
    Tendsto (fun r => A (inverseRadius r)) atTop (𝓝 (A 0)) ∧
    Tendsto (reciprocalDerivative A) atTop (𝓝 0) ∧
    ∀ᶠ r in atTop, HasDerivAt (fun s => A (inverseRadius s))
      (reciprocalDerivative A r/radiusLapse r) r := by
  have val := ah.continuousAt.tendsto.comp inverse_radius_tends_to_zero
  have der := ah.deriv.continuousAt.tendsto.comp inverse_radius_tends_to_zero
  have jet := lapse_tends_to_one.mul (der.mul ((inverse_radius_tends_to_zero.pow 2).neg))
  refine ⟨val,?_,?_⟩
  · change Tendsto (fun r : ℝ => radiusLapse r*(deriv A (inverseRadius r)*(-(inverseRadius r)^2)))
      atTop (𝓝 0)
    simpa [Function.comp_def] using jet
  · filter_upwards [inverse_radius_tends_to_zero.eventually ah.eventually_analyticAt,
      eventually_gt_atTop (2:ℝ)] with r near hr
    have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
    have dh := (near.differentiableAt.hasDerivAt.comp (r : ℂ) (hasDerivAt_inv nz)).comp_ofReal
    apply dh.congr_deriv
    rw [reciprocalDerivative,mul_div_cancel_left₀ _ (exterior_lapse_nonzero hr),inverseRadius,inv_pow]

theorem reciprocal_row_limits (A : ℂ → Coefficients)
    (h₁ : AnalyticAt ℂ (fun z => (A z).1) 0) (h₂ : AnalyticAt ℂ (fun z => (A z).2.1) 0)
    (h₃ : AnalyticAt ℂ (fun z => (A z).2.2) 0) :
    CoefficientLimits radiusLapse (reciprocalValue A) (reciprocalJet A) (A 0) := by
  obtain ⟨a,da,ea⟩ := reciprocal_component _ h₁
  obtain ⟨b,db,eb⟩ := reciprocal_component _ h₂
  obtain ⟨c,dc,ec⟩ := reciprocal_component _ h₃
  refine ⟨?_,da.prodMk_nhds (db.prodMk_nhds dc),?_⟩
  · have lim := a.prodMk_nhds (b.prodMk_nhds c)
    unfold reciprocalValue
    convert lim using 1
  · filter_upwards [ea,eb,ec] with r x y z
    exact ⟨x,y,z⟩

theorem exterior_horizon_radius :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 (2 : ℂ)) := by
  simpa only [Complex.ofReal_ofNat] using
    (Complex.continuous_ofReal.continuousAt (x := (2:ℝ))).tendsto.mono_left nhdsWithin_le_nhds

def horizonDerivative (H : ℂ → ℂ) (r : ℝ) : ℂ := radiusLapse r*deriv H (r : ℂ)

theorem horizon_envelope_limits (H : ℂ → ℂ) (ah : AnalyticAt ℂ H 2) :
    Tendsto (fun r : ℝ => H (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 (H 2)) ∧
    Tendsto (horizonDerivative H) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
  have quot := (exterior_horizon_radius.sub (tendsto_const_nhds (x := (2:ℂ)))).div
    exterior_horizon_radius (by norm_num : (2:ℂ) ≠ 0)
  have vanish := quot.mul (ah.deriv.continuousAt.tendsto.comp exterior_horizon_radius)
  refine ⟨ah.continuousAt.tendsto.comp exterior_horizon_radius,?_⟩
  change Tendsto (fun r : ℝ => ((r : ℂ)-2)/(r : ℂ)*deriv H (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 0)
  simpa [Function.comp_def] using vanish

/-- Differentiate an actual exterior equality with the analytic
ingoing envelope. This also fixes the sign of the horizon wave jet. -/
theorem ingoing_exterior_jet (w : ℂ) (c v dv : ℝ → ℂ) (H : ℂ → ℂ) (ah : AnalyticAt ℂ H 2)
    (carrier : ∀ r, 2 < r → HasDerivAt c (-w*c r/radiusLapse r) r)
    (value : ∀ᶠ r in 𝓝[>] (2 : ℝ), v r = c r*H (r : ℂ))
    (jet : ∀ r, 2 < r → HasDerivAt v (dv r/radiusLapse r) r) :
    ∀ᶠ r in 𝓝[>] (2 : ℝ), dv r = c r*(horizonDerivative H r-w*H (r : ℂ)) := by
  filter_upwards [eventually_eventually_nhdsWithin.2 value,
    exterior_horizon_radius.eventually ah.eventually_analyticAt,self_mem_nhdsWithin] with r ev ha hr
  have openSide : 𝓝[Set.Ioi (2 : ℝ)] r = 𝓝 r := by
    exact nhdsWithin_eq_nhds.mpr (Ioi_mem_nhds hr)
  have loc : v =ᶠ[𝓝 r] fun t => c t*H (t : ℂ) := by
    rwa [openSide] at ev
  have dj := (carrier r hr).mul ha.differentiableAt.hasDerivAt.comp_ofReal
  have derived := (dj.congr_of_eventuallyEq loc).unique (jet r hr)
  unfold horizonDerivative
  have fn := exterior_lapse_nonzero hr
  apply (div_left_inj' fn).1
  rw [← derived]
  field_simp [fn] <;> ring

theorem ingoing_analytic_current_zero (w : ℂ) (c u du p dp : ℝ → ℂ) (U P : ℂ → ℂ)
    (uAnalytic : AnalyticAt ℂ U 2) (pAnalytic : AnalyticAt ℂ P 2)
    (unit : ∀ r, ‖c r‖ = 1) (carrier : ∀ r, 2 < r → HasDerivAt c (-w*c r/radiusLapse r) r)
    (uValue : ∀ᶠ r in 𝓝[>] (2 : ℝ), u r = c r*U (r : ℂ))
    (pValue : ∀ᶠ r in 𝓝[>] (2 : ℝ), p r = c r*P (r : ℂ))
    (uJet : ∀ r, 2 < r → HasDerivAt u (du r/radiusLapse r) r)
    (pJet : ∀ r, 2 < r → HasDerivAt p (dp r/radiusLapse r) r) :
    Tendsto (radialCurrent u du p dp) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
  obtain ⟨uLim,dULim⟩ := horizon_envelope_limits U uAnalytic
  obtain ⟨pLim,dPLim⟩ := horizon_envelope_limits P pAnalytic
  have h := ingoing_current_limit (𝓝[>] (2 : ℝ)) w c (fun r => U (r : ℂ)) (horizonDerivative U)
    (fun r => P (r : ℂ)) (horizonDerivative P) unit _ _ uLim pLim dULim dPLim
  apply h.congr'
  filter_upwards [uValue,pValue,ingoing_exterior_jet w c u du U uAnalytic carrier uValue uJet,
    ingoing_exterior_jet w c p dp P pAnalytic carrier pValue pJet] with r a b a' b'
  rw [radialCurrent,a,b,a',b']

#print axioms reciprocal_row_limits
#print axioms potential_tends_to_frequency
#print axioms ingoing_exterior_jet
#print axioms ingoing_analytic_current_zero

end
end SchwarzschildLaurent.Outgoing
