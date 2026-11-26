import OutgoingMixtureHorizon
import LinearInverseSquareLimit
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Amplitudes extracted from an actual wave and its tortoise jet.
Their evolution in areal radius has an integrable inverse-square bound. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set
open scoped Topology
open SchwarzschildLaurent.Outgoing SchwarzschildMixtures SchwarzschildMixtures.Strain

noncomputable section

def incomingCarrier (w : ℂ) (r : ℝ) : ℂ := phase (-w) (realTortoise r)
def outgoingCarrier (w : ℂ) (r : ℝ) : ℂ := phase w (realTortoise r)

def tailPotential (L : ℂ) (r : ℝ) : ℂ := L/(r : ℂ)^2-6/(r : ℂ)^3

def modalCoefficients (w : ℂ) (u du : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  (incomingMode w (outgoingCarrier w r) (u r) (du r),
    outgoingMode w (incomingCarrier w r) (u r) (du r))

def modalDerivative (w L : ℂ) (r : ℝ) (a : ℂ × ℂ) : ℂ × ℂ :=
  let response := tailPotential L r*wave a.1 a.2 (incomingCarrier w r) (outgoingCarrier w r)/(2*w)
  (-(outgoingCarrier w r*response), incomingCarrier w r*response)

private theorem outgoing_carrier_derivative (w : ℂ) (r : ℝ) (hr : 2 < r) :
    HasDerivAt (outgoingCarrier w) (w*outgoingCarrier w r/radiusLapse r) r := by
  change HasDerivAt (fun s => phase w (realTortoise s)) _ r
  simpa only [outgoingCarrier,neg_neg] using exterior_carrier_derivative (-w) r hr

theorem modal_coefficients_derivative (w L : ℂ) (hw : w ≠ 0)
    (u du : ℝ → ℂ) (r : ℝ) (hr : 2 < r)
    (equation : RadialEquation radiusLapse (rwPotential w L) 0 u du) :
    HasDerivAt (modalCoefficients w u du) (modalDerivative w L r (modalCoefficients w u du r)) r := by
  let a := modalCoefficients w u du r
  let m := incomingCarrier w
  let p := outgoingCarrier w
  let X := tailPotential L r*u r/(2*w)
  have ph : m r*p r = 1 := opposite_phases w (realTortoise r)
  have wave_eq : wave a.1 a.2 (m r) (p r) = u r :=
    (reconstruct_modes w (m r) (p r) (u r) (du r) hw ph).1
  have hV : rwPotential w L r = w^2+radiusLapse r*tailPotential L r := rfl
  have f0 : radiusLapse r ≠ 0 := exterior_lapse_nonzero hr
  have first0 := (((equation.value r hr).sub ((equation.jet r hr).div_const w)).mul
    (outgoing_carrier_derivative w r hr)).div_const 2
  have dm : HasDerivAt m (-w*m r/radiusLapse r) r := exterior_carrier_derivative w r hr
  have second0 := (((equation.value r hr).add ((equation.jet r hr).div_const w)).mul
    dm).div_const 2
  have first : HasDerivAt (fun s => incomingMode w (p s) (u s) (du s)) (-(p r*X)) r := by
    apply first0.congr_deriv
    simp only [hV,Pi.zero_apply,add_zero,Pi.sub_apply]
    change _ = -(p r*(tailPotential L r*u r/(2*w)))
    field_simp [f0,hw]
    ring
  have second : HasDerivAt (fun s => outgoingMode w (m s) (u s) (du s)) (m r*X) r := by
    apply second0.congr_deriv
    simp only [hV,Pi.zero_apply,add_zero,Pi.add_apply]
    change _ = m r*(tailPotential L r*u r/(2*w))
    field_simp [f0,hw]
    ring
  apply (first.prodMk second).congr_deriv
  change (-(p r*X),m r*X) =
    (-(p r*(tailPotential L r*wave a.1 a.2 (m r) (p r)/(2*w))),
      m r*(tailPotential L r*wave a.1 a.2 (m r) (p r)/(2*w)))
  rw [wave_eq]

theorem norm_tail_potential (L : ℂ) (r : ℝ) (hr : 2 < r) :
    ‖tailPotential L r‖ ≤ (‖L‖+3)/r^2 := by
  have pos : 0 < r := by linarith
  have six : (6:ℝ)/r ≤ 3 := (div_le_iff₀ pos).2 (by linarith)
  have third : (6:ℝ)/r^3 ≤ 3/r^2 := by
    rw [pow_succ, mul_comm (r^2) r,div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right six (sq_nonneg _)
  calc
    _ ≤ ‖L/(r : ℂ)^2‖+‖(6:ℂ)/(r : ℂ)^3‖ := norm_sub_le _ _
    _ = ‖L‖/r^2+6/r^3 := by
      simp [norm_pow,Complex.norm_real,abs_of_pos pos]
    _ ≤ _ := by rw [add_div]; exact add_le_add le_rfl third

theorem modal_derivative_bound (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (r : ℝ) (hr : 2 < r) (a : ℂ × ℂ) :
    ‖modalDerivative w L r a‖ ≤ (((‖L‖+3)/‖w‖)/r^2)*‖a‖ := by
  let m := incomingCarrier w r
  let p := outgoingCarrier w r
  have nm : ‖m‖ = 1 := phase_norm (-w) (by simp [wi]) (realTortoise r)
  have np : ‖p‖ = 1 := phase_norm w wi (realTortoise r)
  have value : ‖wave a.1 a.2 m p‖ ≤ 2*‖a‖ := calc
    _ ≤ ‖a.1*m‖+‖a.2*p‖ := norm_add_le _ _
    _ = ‖a.1‖+‖a.2‖ := by simp [nm,np]
    _ ≤ ‖a‖+‖a‖ := add_le_add (norm_fst_le a) (norm_snd_le a)
    _ = _ := by ring
  have nw : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  change ‖(-(p*(tailPotential L r*wave a.1 a.2 m p/(2*w))),
      m*(tailPotential L r*wave a.1 a.2 m p/(2*w)))‖ ≤ _
  simp only [Prod.norm_def,norm_neg,norm_mul,np,nm,one_mul,max_self,norm_div,Complex.norm_ofNat]
  calc
    _ ≤ ((‖L‖+3)/r^2)*(2*‖a‖)/(2*‖w‖) := by
      have tail_bound := norm_tail_potential L r hr
      gcongr
    _ = _ := by simp only [Prod.norm_def]; ring

/-- Both leading coefficients exist for any homogeneous exterior wave.
The error bound is joint for the value and the tortoise derivative
through their exact modal decomposition. -/
theorem rw_scattering_limits (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0) (u du : ℝ → ℂ)
    (eq : RadialEquation radiusLapse (rwPotential w L) 0 u du) :
    ∃ ain aout : ℂ,
      ModeLimits atTop w (incomingCarrier w) (outgoingCarrier w) u du ain aout ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 3 ≤ r →
          ‖modalCoefficients w u du r-(ain,aout)‖ ≤ M/r := by
  let A := modalCoefficients w u du
  obtain ⟨⟨ain,aout⟩,ha,M,m0,rem⟩ := inverse_square_limit A (fun r => modalDerivative w L r (A r))
    ((‖L‖+3)/‖w‖) (by positivity)
    (fun r hr => modal_coefficients_derivative w L hw u du r hr eq)
    (fun r hr => modal_derivative_bound w L hw wi r hr (A r))
  have first := (continuous_fst.continuousAt (x := (ain,aout))).tendsto.comp ha
  have second := (continuous_snd.continuousAt (x := (ain,aout))).tendsto.comp ha
  exact ⟨ain,aout,⟨first,second⟩,M,m0,rem⟩

#print axioms modal_coefficients_derivative
#print axioms rw_scattering_limits

end
end SchwarzschildLaurent.LinearWave
