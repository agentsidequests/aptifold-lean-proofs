import HorizonFrobeniusEquation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Restore the manuscript's ingoing carrier on the Schwarzschild exterior. -/
namespace SchwarzschildLaurent.Horizon

open Filter
open scoped Topology

noncomputable section

def radialLapse (r : ℂ) : ℂ := (r-2)/r

def tortoise (r : ℂ) : ℂ := r+2*Complex.log (r/2-1)

def ingoingCarrier (k r : ℂ) : ℂ := Complex.exp (-k*tortoise r)

def tortoiseDifferential (J : ℂ → ℂ) (r : ℂ) : ℂ := radialLapse r*deriv J r

def ingoingWave (k : ℂ) (H : ℂ → ℂ) (r : ℂ) : ℂ := ingoingCarrier k r*H r

private theorem horizon_ne {r : ℂ} (cut : r/2-1 ∈ Complex.slitPlane) : r-2 ≠ 0 := by
  intro e
  apply Complex.slitPlane_ne_zero cut
  linear_combination e/2

theorem tortoise_has_derivative {r : ℂ} (cut : r/2-1 ∈ Complex.slitPlane) :
    HasDerivAt tortoise (r/(r-2)) r := by
  have arg := ((hasDerivAt_id r).div_const (2 : ℂ)).sub_const 1
  have log := (Complex.hasDerivAt_log cut).comp r arg
  apply ((hasDerivAt_id r).add (log.const_mul 2)).congr_deriv
  change 1+2*((r/2-1)⁻¹*(1/2)) = r/(r-2)
  field_simp [Complex.slitPlane_ne_zero cut, horizon_ne cut]
  ring

theorem exterior_log_argument (r : ℝ) (hr : 2 < r) : (r : ℂ)/2-1 ∈ Complex.slitPlane := by
  have positive : 0 < r/2-1 := by linarith
  simpa using (Complex.ofReal_mem_slitPlane.2 positive)

theorem tortoise_real_exterior (r : ℝ) (hr : 2 < r) :
    tortoise (r : ℂ) = ((r+2*Real.log (r/2-1) : ℝ) : ℂ) := by
  have h : 0 ≤ r/2-1 := by linarith
  simp [tortoise, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_log h]

set_option maxHeartbeats 800000 in
theorem carrier_has_derivative (k : ℂ) {r : ℂ} (cut : r/2-1 ∈ Complex.slitPlane) :
    HasDerivAt (ingoingCarrier k) (-k*(r/(r-2))*ingoingCarrier k r) r := by
  have derive := (Complex.hasDerivAt_exp (-k*tortoise r)).comp r ((tortoise_has_derivative cut).const_mul (-k))
  exact derive.congr_deriv (by unfold ingoingCarrier; ring)

theorem ingoing_wave_first_derivative (k : ℂ) {H : ℂ → ℂ} {r : ℂ}
    (cut : r/2-1 ∈ Complex.slitPlane) (hr : r ≠ 0) (hH : DifferentiableAt ℂ H r) :
    tortoiseDifferential (ingoingWave k H) r =
      ingoingCarrier k r*(radialLapse r*deriv H r-k*H r) := by
  have eq := ((carrier_has_derivative k cut).mul hH.hasDerivAt).deriv
  unfold tortoiseDifferential
  rw [show deriv (ingoingWave k H) r = _ from eq]
  unfold radialLapse
  field_simp [hr, horizon_ne cut]
  ring

def normalizedEnvelope (k L : ℂ) (r : ℂ) : ℂ := ingoingEnvelope k L (r-2)

theorem normalized_envelope_analytic (k L : ℂ) (ki : k.re = 0) :
    AnalyticAt ℂ (normalizedEnvelope k L) 2 := by
  change AnalyticAt ℂ (fun r => ingoingEnvelope k L (r-2)) 2
  simpa only [zero_add] using ((ingoing_has_power_series k L ki).comp_sub 2).analyticAt

@[simp] theorem normalized_envelope_horizon (k L : ℂ) : normalizedEnvelope k L 2 = 1 := by
  simp [normalizedEnvelope]

theorem normalized_envelope_radial_derivative (k L : ℂ) (ki : k.re = 0) :
    deriv (normalizedEnvelope k L) 2 = (L-3)/(2*(1-4*k)) := by
  change deriv (fun r => ingoingEnvelope k L (r-2)) 2 = _
  rw [deriv_comp_sub_const, sub_self, ingoing_envelope_derivative k L ki]

/-- The same phase-removed equation in areal radius rather than \(s=r-2\). -/
def arealHorizonResidual (k L : ℂ) (H : ℂ → ℂ) (r : ℂ) : ℂ :=
  (r-2)*r^2*deriv (deriv H) r+(2*r-2*k*r^3)*deriv H r+(6-L*r)*H r

theorem normalized_envelope_residual (k L : ℂ) (ki : k.re = 0) :
    ∀ᶠ r in 𝓝 (2 : ℂ), arealHorizonResidual k L (normalizedEnvelope k L) r = 0 := by
  have translate : Tendsto (fun r : ℂ => r-2) (𝓝 2) (𝓝 0) := by
    have cont : ContinuousAt (fun r : ℂ => r-2) 2 := by fun_prop
    change Tendsto (fun r : ℂ => r-2) (𝓝 2) (𝓝 ((2 : ℂ)-2)) at cont
    simpa only [sub_self] using cont
  have first : deriv (normalizedEnvelope k L) = fun r => deriv (ingoingEnvelope k L) (r-2) := by
    funext r
    exact deriv_comp_sub_const _ _ _
  filter_upwards [translate.eventually (ingoing_envelope_equation k L ki)] with r eq
  simpa only [arealHorizonResidual, normalizedEnvelope, first, deriv_comp_sub_const, horizonResidual,
    sub_add_cancel] using eq

theorem scaled_envelope_residual (k L a : ℂ) (ki : k.re = 0) :
    ∀ᶠ r in 𝓝 (2 : ℂ), arealHorizonResidual k L (fun r => a*normalizedEnvelope k L r) r = 0 := by
  have f := normalized_envelope_analytic k L ki
  filter_upwards [f.eventually_analyticAt,normalized_envelope_residual k L ki] with r h eq
  have first : deriv (fun z => a*normalizedEnvelope k L z) =ᶠ[𝓝 r]
      (fun z => a*deriv (normalizedEnvelope k L) z) := by
    filter_upwards [h.eventually_analyticAt] with z hz
    exact (hz.differentiableAt.hasDerivAt.const_mul a).deriv
  rw [arealHorizonResidual, first.deriv_eq, first.eq_of_nhds,
    (h.deriv.differentiableAt.hasDerivAt.const_mul a).deriv]
  unfold arealHorizonResidual at eq
  linear_combination a*eq

/-- Restoring the carrier gives the Regge–Wheeler wave equation. -/
theorem ingoing_wave_from_envelope (k L : ℂ) {H : ℂ → ℂ} {r : ℂ}
    (cut : r/2-1 ∈ Complex.slitPlane) (hr : r ≠ 0)
    (hH : AnalyticAt ℂ H r) (eq : arealHorizonResidual k L H r = 0) :
    tortoiseDifferential (tortoiseDifferential (ingoingWave k H)) r =
      (k^2+radialLapse r*(L/r^2-6/r^3))*ingoingWave k H r := by
  let B := fun z => radialLapse z*deriv H z-k*H z
  have open_cut : IsOpen {z : ℂ | z/2-1 ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (by fun_prop)
  have first : tortoiseDifferential (ingoingWave k H) =ᶠ[𝓝 r] ingoingWave k B := by
    filter_upwards [open_cut.mem_nhds cut,eventually_ne_nhds hr,hH.eventually_analyticAt] with z hz hn ha
    exact ingoing_wave_first_derivative k hz hn ha.differentiableAt
  have lapse : HasDerivAt radialLapse (2/r^2) r := by
    have raw := ((hasDerivAt_id r).sub_const 2).div (hasDerivAt_id r) hr
    apply raw.congr_deriv
    simp only [id_eq]
    ring
  have dB : HasDerivAt B
      (2/r^2*deriv H r+radialLapse r*deriv (deriv H) r-k*deriv H r) r :=
    (lapse.mul hH.deriv.differentiableAt.hasDerivAt).sub (hH.differentiableAt.hasDerivAt.const_mul k)
  change radialLapse r*deriv (tortoiseDifferential (ingoingWave k H)) r = _
  rw [first.deriv_eq]
  change tortoiseDifferential (ingoingWave k B) r = _
  rw [ingoing_wave_first_derivative k cut hr dB.differentiableAt, dB.deriv]
  apply sub_eq_zero.mp
  calc
    _ = (ingoingCarrier k r*(r-2)/r^4)*arealHorizonResidual k L H r := by
      dsimp only [B, ingoingWave, radialLapse, arealHorizonResidual]
      field_simp [hr]
      ring
    _ = 0 := by rw [eq, mul_zero]

#print axioms tortoise_has_derivative
#print axioms tortoise_real_exterior
#print axioms ingoing_wave_first_derivative
#print axioms normalized_envelope_analytic
#print axioms normalized_envelope_residual
#print axioms scaled_envelope_residual
#print axioms ingoing_wave_from_envelope

end
end SchwarzschildLaurent.Horizon
