import OutgoingMixtureInfinity
import OutgoingFlux
import AdmittedFutureHorizon

/-! Bind the analytic horizon algebra to the manuscript's radial
coordinate and the already checked ingoing solutions. -/
namespace SchwarzschildMixtures.Strain

open SchwarzschildLaurent.Horizon SchwarzschildLaurent.Outgoing SchwarzschildMixtures.OutgoingData
open Filter Set
open scoped Topology

noncomputable section

def horizonEnvelope (w L scale : ℂ) (r : ℂ) : ℂ := scale*normalizedEnvelope w L r

def horizonBranch (w L scale : ℂ) (r : ℝ) : ℂ :=
  ingoingWave w (horizonEnvelope w L scale) (r : ℂ)

private theorem horizon_envelope_analytic (w L scale : ℂ) (wi : w.re = 0) :
    AnalyticAt ℂ (horizonEnvelope w L scale) 2 :=
  (analyticAt_const (v := scale)).fun_mul (normalized_envelope_analytic w L wi)

private theorem phase_eq_carrier (w : ℂ) (r : ℝ) (hr : 2 < r) :
    phase (-w) (realTortoise r) = ingoingCarrier w (r : ℂ) := by
  unfold phase ingoingCarrier
  rw [tortoise_real_exterior r hr]
  rfl

theorem exterior_carrier_derivative (w : ℂ) (r : ℝ) (hr : 2 < r) :
    HasDerivAt (fun s => phase (-w) (realTortoise s))
      (-w*phase (-w) (realTortoise r)/radiusLapse r) r := by
  have e : (fun s => phase (-w) (realTortoise s)) =ᶠ[𝓝 r] (fun s : ℝ => ingoingCarrier w (s : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact phase_eq_carrier w s hs
  apply (((carrier_has_derivative w (exterior_log_argument r hr)).comp_ofReal).congr_of_eventuallyEq e).congr_deriv
  have nr : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  have gap : (r : ℂ)-2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hr.ne')
  rw [phase_eq_carrier _ _ hr,radiusLapse]
  field_simp [nr,gap]

private theorem carrier_branch (w L scale : ℂ) (u : ℝ → ℂ)
    (value : u =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch w L scale) :
    ∀ᶠ r in 𝓝[>] (2 : ℝ), u r = phase (-w) (realTortoise r)*horizonEnvelope w L scale (r : ℂ) := by
  filter_upwards [value,self_mem_nhdsWithin] with r h hr
  rw [h,phase_eq_carrier _ _ (show 2 < r from hr)]
  rfl

theorem normalized_horizon_envelope (w L scale : ℂ) (wi : w.re = 0) (u : ℝ → ℂ)
    (value : u =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch w L scale) :
    AnalyticAt ℂ (horizonEnvelope w L scale) 2 ∧
    ∀ᶠ r in 𝓝[>] (2 : ℝ), u r = phase (-w) (realTortoise r)*horizonEnvelope w L scale (r : ℂ) :=
  ⟨horizon_envelope_analytic w L scale wi,carrier_branch w L scale u value⟩

theorem normalized_horizon_modes (w L a : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (u du : ℝ → ℂ) (value : u =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch w L a)
    (jet : ∀ r, 2 < r → HasDerivAt u (du r/radiusLapse r) r) :
    ModeLimits (𝓝[>] (2 : ℝ)) w (fun r => phase (-w) (realTortoise r))
      (fun r => phase w (realTortoise r)) u du a 0 := by
  have modes := ingoing_analytic_mode_limits w hw wi realTortoise u du (horizonEnvelope w L a)
    (horizon_envelope_analytic w L a wi) (exterior_carrier_derivative w)
    (carrier_branch w L a u value) jet
  simpa only [horizonEnvelope,normalized_envelope_horizon,mul_one] using modes

private theorem particular_is_exterior_daughter (second : Bool) (n : ℕ) (k : ℂ)
    (J : ℂ → ℂ) (r : ℝ) :
    radialParticular second n k (fun a : ℝ => J (a : ℂ))
      (fun a : ℝ => tortoiseDifferential J (a : ℂ)) r = exteriorDaughter second n k J 0 r := by
  simp only [radialParticular,effectiveFieldCoefficients,quadraticValue,exteriorDaughter,
    evaluateEnvelopeAt,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  ring

theorem admitted_horizon_envelope (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k a : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (j dj : ℝ → ℂ)
    (parent : j =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch k ((n : ℂ)*(n+1)) a)
    (jet : ∀ r, 2 < r → HasDerivAt j (dj r/radiusLapse r) r) :
    ∃ P : ℂ → ℂ, AnalyticAt ℂ P 2 ∧
      ∀ᶠ r in 𝓝[>] (2 : ℝ), radialParticular second n k j dj r =
        phase (-(2*k)) (realTortoise r)*P (r : ℂ) := by
  let L : ℂ := (n : ℂ)*(n+1)
  let H := horizonEnvelope k L a
  let J := ingoingWave k H
  have hH := horizon_envelope_analytic k L a ki
  obtain ⟨P,pa,pe⟩ := admitted_future_horizon_of_envelope second n hn k hk ki H hH
  have pair : AnalyticAt ℂ (fun r : ℂ => ((0:ℂ),r)) 2 := by fun_prop
  have pa' : AnalyticAt ℂ P 2 := by
    simpa [ingoingDaughter] using (pa 0).fun_comp_of_eq pair rfl
  refine ⟨P,pa',?_⟩
  have pjet := ingoing_exterior_jet k _ j dj H hH (exterior_carrier_derivative k)
    (carrier_branch k L a j parent) jet
  filter_upwards [parent,pjet,pe,exterior_horizon_radius.eventually hH.eventually_analyticAt,
    self_mem_nhdsWithin] with r jval dval ev hrH hrr
  have hr : 2 < r := hrr
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  have dz : dj r = tortoiseDifferential J (r : ℂ) := by
    rw [dval,phase_eq_carrier _ _ hr]
    exact (ingoing_wave_first_derivative k (exterior_log_argument r hr) nz hrH.differentiableAt).symm
  calc
    _ = radialParticular second n k (fun s : ℝ => J (s : ℂ)) (fun s : ℝ => tortoiseDifferential J (s : ℂ)) r := by
      unfold radialParticular
      rw [show j r = J (r : ℂ) from jval,dz]
    _ = exteriorDaughter second n k J 0 r := particular_is_exterior_daughter second n k J r
    _ = _ := by simpa [ingoingDaughter,phase] using ev 0

theorem admitted_particular_horizon_current (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k a transmission : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (j dj u du dp : ℝ → ℂ)
    (jValue : j =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch k ((n : ℂ)*(n+1)) a)
    (uValue : u =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch (2*k) ((2*(n : ℂ))*(2*n+1)) transmission)
    (jJet : ∀ r, 2 < r → HasDerivAt j (dj r/radiusLapse r) r)
    (uJet : ∀ r, 2 < r → HasDerivAt u (du r/radiusLapse r) r)
    (pJet : ∀ r, 2 < r → HasDerivAt (radialParticular second n k j dj) (dp r/radiusLapse r) r) :
    Tendsto (radialCurrent u du (radialParticular second n k j dj) dp) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
  obtain ⟨P,pa,pv⟩ := admitted_horizon_envelope second n hn k a hk ki j dj jValue jJet
  have wIm : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  exact ingoing_analytic_current_zero (2*k) _ u du _ dp _ P
    (horizon_envelope_analytic _ _ _ wIm) pa
    (fun r => phase_norm (-(2*k)) (by simp [wIm]) _) (exterior_carrier_derivative _)
    (carrier_branch _ _ _ u uValue) pv uJet pJet

#print axioms exterior_carrier_derivative
#print axioms normalized_horizon_envelope
#print axioms normalized_horizon_modes
#print axioms admitted_horizon_envelope
#print axioms admitted_particular_horizon_current

end
end SchwarzschildMixtures.Strain
