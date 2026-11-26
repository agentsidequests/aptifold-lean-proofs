import LinearExteriorWave
import OutgoingStrainNormalization

/-! Normalize the actual global waves in the scattering convention used
for the two admitted Schwarzschild fields. -/
namespace SchwarzschildLaurent.LinearWave

open Filter ComplexConjugate
open scoped Topology
open SchwarzschildLaurent.Outgoing SchwarzschildLaurent.Horizon
open SchwarzschildMixtures SchwarzschildMixtures.Strain

noncomputable section

def angularEigenvalue (n : ℕ) : ℂ := (n : ℂ)*(n+1)

theorem angular_eigenvalue_double (n : ℕ) :
    angularEigenvalue (2*n) = 2*(n : ℂ)*(2*n+1) := by
  unfold angularEigenvalue
  push_cast
  rfl

structure IngoingWaveData (w L scale : ℂ) where
  value : ℝ → ℂ
  jet : ℝ → ℂ
  incoming : ℂ
  outgoing : ℂ
  equation : RadialEquation radiusLapse (rwPotential w L) 0 value jet
  horizon : value =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch w L scale
  infinity : ModeLimits atTop w (incomingCarrier w) (outgoingCarrier w) value jet incoming outgoing
  remainder : ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 3 ≤ r →
    ‖modalCoefficients w value jet r-(incoming,outgoing)‖ ≤ M/r

theorem exists_ingoing_scattering_wave (w L scale : ℂ) (hw : w ≠ 0) (wi : w.re = 0) :
    Nonempty (IngoingWaveData w L scale) := by
  obtain ⟨u,du,eq,horizon⟩ := global_regge_wheeler_wave w L scale wi
  obtain ⟨ain,aout,atInfinity,rem⟩ := rw_scattering_limits w L hw wi u du eq
  exact ⟨⟨u,du,ain,aout,eq,horizon,atInfinity,rem⟩⟩

theorem ingoing_scattering_flux (w : ℂ) (hw : w ≠ 0) (wi : w.re = 0) (n : ℕ) (a : ℂ)
    (u : IngoingWaveData w (angularEigenvalue n) a) :
    Complex.normSq u.incoming = Complex.normSq u.outgoing+Complex.normSq a := by
  have real (r : ℝ) :
      conj (rwPotential w (angularEigenvalue n) r) = rwPotential w (angularEigenvalue n) r := by
    have aux := rw_potential_is_real w wi ((n : ℝ)*(n+1)) r
    push_cast at aux
    exact aux
  have atHorizon := normalized_horizon_modes w (angularEigenvalue n) a hw wi u.value u.jet u.horizon u.equation.value
  exact flux_balance w hw wi realTortoise radiusLapse _ u.value u.jet lapse_is_real real u.equation
    u.incoming u.outgoing a u.infinity atHorizon

theorem scaled_radial_equation (f V u du : ℝ → ℂ) (c : ℂ)
    (eq : RadialEquation f V 0 u du) :
    RadialEquation f V 0 (fun r => c*u r) (fun r => c*du r) := by
  constructor <;> intro r hr
  · simpa only [mul_div_assoc] using (eq.value r hr).const_mul c
  · apply ((eq.jet r hr).const_mul c).congr_deriv
    simp only [Pi.zero_apply,add_zero,← mul_div_assoc]
    ring

private theorem scale_modal_coefficients (w c : ℂ) (u du : ℝ → ℂ) (r : ℝ) :
    modalCoefficients w (fun s => c*u s) (fun s => c*du s) r =
      c • modalCoefficients w u du r := by
  refine Prod.ext ?_ ?_ <;>
    simp only [modalCoefficients,incomingMode,outgoingMode,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

/-- Changing the incoming normalization rescales both complex amplitudes
and the same horizon solution. -/
def IngoingWaveData.scale {w L a : ℂ} (u : IngoingWaveData w L a) (c : ℂ) :
    IngoingWaveData w L (c*a) where
  value := fun r => c*u.value r
  jet := fun r => c*u.jet r
  incoming := c*u.incoming
  outgoing := c*u.outgoing
  equation := scaled_radial_equation _ _ _ _ _ u.equation
  horizon := by
    filter_upwards [u.horizon] with r hr
    rw [hr]
    unfold horizonBranch horizonEnvelope ingoingWave
    ring
  infinity := by
    refine ⟨(u.infinity.incoming.const_mul c).congr ?_,
      (u.infinity.outgoing.const_mul c).congr ?_⟩ <;> intro r
    · exact (congrArg Prod.fst (scale_modal_coefficients w c u.value u.jet r)).symm
    · exact (congrArg Prod.snd (scale_modal_coefficients w c u.value u.jet r)).symm
  remainder := by
    obtain ⟨M,m0,rest⟩ := u.remainder
    refine ⟨‖c‖*M,mul_nonneg (norm_nonneg _) m0,?_⟩
    intro r hr
    rw [scale_modal_coefficients, show (c*u.incoming,c*u.outgoing) = c • (u.incoming,u.outgoing) from rfl,
      ← smul_sub,norm_smul,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (rest r hr) (norm_nonneg _)

/-- The odd reference parent has incoming coefficient alpha and the
odd daughter has unit horizon normalization. Both are defined globally. -/
theorem global_strain_scattering_data (n : ℕ) (hn : 2 ≤ n) (k : ℂ)
    (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
        j.incoming = parentAlpha k n ∧ a ≠ 0 ∧ u.incoming ≠ 0 := by
  have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  obtain ⟨j⟩ := exists_ingoing_scattering_wave k (angularEigenvalue n) 1 hk ki
  obtain ⟨u⟩ := exists_ingoing_scattering_wave (2*k) (angularEigenvalue (2*n)) 1 wk wi
  have hJ := nonzero_incident_amplitude (ingoing_scattering_flux k hk ki n 1 j) (by norm_num)
  have hU := nonzero_incident_amplitude (ingoing_scattering_flux (2*k) wk wi (2*n) 1 u) (by norm_num)
  have α0 : parentAlpha k n ≠ 0 := by
    unfold parentAlpha
    exact div_ne_zero (gamma_add_frequency n hn k ki)
      (by simpa only [sub_eq_add_neg] using gamma_add_frequency n hn (-k) (by simp [ki]))
  let c := parentAlpha k n/j.incoming
  refine ⟨c*1,j.scale c,u,?_,mul_ne_zero (div_ne_zero α0 hJ) one_ne_zero,hU⟩
  change parentAlpha k n/j.incoming*j.incoming = parentAlpha k n
  exact div_mul_cancel₀ _ hJ

#print axioms exists_ingoing_scattering_wave
#print axioms ingoing_scattering_flux
#print axioms global_strain_scattering_data

end
end SchwarzschildLaurent.LinearWave
