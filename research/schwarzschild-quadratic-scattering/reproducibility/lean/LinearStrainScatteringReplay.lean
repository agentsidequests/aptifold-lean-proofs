import LinearZerilliEquation
import OutgoingStrainReplay

/-! The global linear inputs for the exact outgoing-strain identity.
The even parent is related to the odd reference by the normalized
Darboux map on the entire exterior. -/
namespace SchwarzschildLaurent.LinearWave

open Filter MeasureTheory
open scoped Topology Interval
open SchwarzschildLaurent.Outgoing SchwarzschildLaurent.Horizon
open SchwarzschildMixtures SchwarzschildMixtures.Strain

noncomputable section

private theorem even_partner_horizon (n : ℕ) (hn : 2 ≤ n) (w a : ℂ) (wi : w.re = 0)
    (j : IngoingWaveData w (angularEigenvalue n) a) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 2 ∧ H 2 = (gamma n-w)*a/(gamma n+w) ∧
      ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ),
        inverseDarbouxValue w (gamma n) (schwarzschildW n (r : ℂ)) (j.value r) (j.jet r) =
          incomingCarrier w r*H (r : ℂ) := by
  let H := horizonEnvelope w (angularEigenvalue n) a
  let G := fun z : ℂ => ((schwarzschildW n z-w)*H z+radialLapse z*deriv H z)/(gamma n+w)
  have analyticH : AnalyticAt ℂ H 2 :=
    (analyticAt_const (v := a)).fun_mul (normalized_envelope_analytic w (angularEigenvalue n) wi)
  obtain ⟨aw,atW⟩ := schwarzschild_superpotential_horizon n hn
  have analyticLapse : AnalyticAt ℂ radialLapse 2 := by
    unfold radialLapse
    exact (show AnalyticAt ℂ (fun z : ℂ => z-2) 2 by fun_prop).fun_div analyticAt_id (by norm_num)
  have aG : AnalyticAt ℂ G 2 := by
    have dH := analyticH.deriv
    unfold G
    fun_prop
  have g0 : G 2 = (gamma n-w)*a/(gamma n+w) := by
    simp only [G,H,atW,horizonEnvelope,normalized_envelope_horizon,radialLapse,sub_self,
      zero_div,mul_one,zero_mul,add_zero]
  have value : ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), j.value r = incomingCarrier w r*H (r : ℂ) := by
    filter_upwards [j.horizon,self_mem_nhdsWithin] with r val hr
    rw [val,horizonBranch,ingoingWave,ingoingCarrier,tortoise_real_exterior r (show 2 < r from hr)]
    rfl
  have jet := ingoing_exterior_jet w (incomingCarrier w) j.value j.jet H analyticH
    (exterior_carrier_derivative w) value j.equation.value
  refine ⟨G,aG,g0,?_⟩
  filter_upwards [value,jet] with r hv hd
  rw [hv,hd]
  unfold inverseDarbouxValue G horizonDerivative
  change _ = incomingCarrier w r *
    (((schwarzschildW n (r : ℂ)-w)*H (r : ℂ)+radiusLapse r*deriv H (r : ℂ))/(gamma n+w))
  ring

/-- A unit-incidence, horizon-ingoing solution of the Zerilli equation.
Its reflection coefficient is exactly the outgoing amplitude of the
odd reference used in the quadratic source. -/
structure EvenParentData (n : ℕ) (w a : ℂ) (j : IngoingWaveData w (angularEigenvalue n) a) where
  value : ℝ → ℂ
  jet : ℝ → ℂ
  equation : RadialEquation radiusLapse (zerilliPotential w n) 0 value jet
  horizon : ∃ H : ℂ → ℂ, AnalyticAt ℂ H 2 ∧ H 2 = (gamma n-w)*a/(gamma n+w) ∧
    ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), value r = incomingCarrier w r*H (r : ℂ)
  infinity : ModeLimits atTop w (incomingCarrier w) (outgoingCarrier w) value jet 1 j.outgoing
  reference : ∀ r : ℝ, 2 < r →
    (schwarzschildW n (r : ℂ)*value r-jet r)/(gamma n-w) = j.value r

def evenParentFromReference (n : ℕ) (hn : 2 ≤ n) (w a : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (j : IngoingWaveData w (angularEigenvalue n) a) (incident : j.incoming = parentAlpha w n) :
    EvenParentData n w a j := by
  have plus : gamma (n : ℂ)+w ≠ 0 := gamma_add_frequency n hn w wi
  have minus : gamma (n : ℂ)-w ≠ 0 := by
    simpa only [sub_eq_add_neg] using gamma_add_frequency n hn (-w) (by simp [wi])
  let W := fun r : ℝ => schwarzschildW n (r : ℂ)
  have h := inverse_darboux_limits w (gamma n) hw wi plus W j.value j.jet
    (schwarzschild_superpotential_limit n hn) j.incoming j.outgoing j.infinity
  have unit : (gamma (n : ℂ)-w)/(gamma (n : ℂ)+w)*j.incoming = 1 := by
    rw [incident,parentAlpha]
    field_simp [plus,minus]
  rw [unit] at h
  exact ⟨_,_,zerilli_partner_equation n hn w a j,even_partner_horizon n hn w a wi j,h,
    fun r _ => darboux_recovers_odd w (gamma n) (W r) (j.value r) (j.jet r) plus minus⟩

/-- Supply the previously assumed global linear waves to the outgoing
strain theorem. The forced radial identity and finite-cutoff integrability
are stated separately from the linear scattering construction. -/
theorem outgoing_strain_with_global_waves (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
        Nonempty (EvenParentData n k a j) ∧ u.incoming ≠ 0 ∧
        ∀ (second : Bool) (dp S : ℝ → ℂ),
          RadialEquation radiusLapse (rwPotential (2*k) (angularEigenvalue (2*n))) S
            (radialParticular second n k j.value j.jet) dp →
          (∀ l r : ℝ, 2 < l → 2 < r →
            IntervalIntegrable (fun x => u.value x*S x/radiusLapse x) volume l r) →
          Tendsto (fun lr : ℝ × ℝ =>
            strainScale second k n *
              ((∫ r in lr.1..lr.2, u.value r*S r/radiusLapse r)/(4*k*u.incoming)))
            ((𝓝[>] (2 : ℝ)) ×ˢ atTop)
            (𝓝 (printedResponse second k n j.outgoing (u.outgoing/u.incoming))) := by
  obtain ⟨a,j,u,incident,_,u0⟩ := global_strain_scattering_data n hn k hk ki
  refine ⟨a,j,u,⟨evenParentFromReference n hn k a hk ki j incident⟩,u0,?_⟩
  intro second dp S pEq finite
  have uEq := u.equation
  have uH := u.horizon
  have pot := congrArg (rwPotential (2*k)) (angular_eigenvalue_double n)
  have hor := congrArg (fun d => horizonBranch (2*k) d 1) (angular_eigenvalue_double n)
  rw [pot] at uEq pEq
  rw [hor] at uH
  have jInf := j.infinity
  rw [incident] at jInf
  exact (admitted_outgoing_strain second n hn k j.outgoing u.incoming u.outgoing a 1 hk ki
    (by norm_num) j.value j.jet u.value u.jet dp S j.equation uEq pEq
    j.horizon uH jInf u.infinity finite).2

#print axioms evenParentFromReference
#print axioms outgoing_strain_with_global_waves

end
end SchwarzschildLaurent.LinearWave
