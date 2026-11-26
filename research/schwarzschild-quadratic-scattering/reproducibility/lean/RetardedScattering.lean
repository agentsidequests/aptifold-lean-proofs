import ExteriorForcedEquation
import LinearRetardedUniqueness
import LinearStrainScatteringReplay

/-! Complete the rational fields to the retarded solutions for the
actual projected regularized sources, with the printed strain. -/
namespace SchwarzschildMixtures.Strain

open Filter SchwarzschildLaurent.Outgoing SchwarzschildLaurent.LinearWave
open SchwarzschildMixtures.OutgoingData
open scoped Topology

noncomputable section

/-- For both admitted mixtures, subtract the incoming daughter amplitude
of the rational field times the unit-incidence homogeneous solution.
The result is the unique retarded field on the exterior. -/
theorem admitted_retarded_scattering (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ a : ℂ, ∃ j : IngoingWaveData k (angularEigenvalue n) a,
      ∃ u : IngoingWaveData (2*k) (angularEigenvalue (2*n)) 1,
        Nonempty (EvenParentData n k a j) ∧ j.incoming = parentAlpha k n ∧ u.incoming ≠ 0 ∧
        ∀ second : Bool,
          let c := (parentAlpha k n)^2*endpointIncoming second k n/u.incoming
          let v := fun r => radialParticular second n k j.value j.jet r-c*u.value r
          let dv := fun r => exteriorParticularJet second n k j.value j.jet r-c*u.jet r
          let q := boundaryResponse second k n j.outgoing (u.outgoing/u.incoming)
          let V := rwPotential (2*k) (angularEigenvalue (2*n))
          let S := exteriorSource second n k j.value j.jet
          RadialEquation radiusLapse V S v dv ∧
          (∃ H : ℂ → ℂ, AnalyticAt ℂ H 2 ∧
            ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), v r = incomingCarrier (2*k) r*H (r : ℂ)) ∧
          RetardedBoundary (2*k) v dv q ∧
          (∀ (other dother : ℝ → ℂ) (out : ℂ),
            RadialEquation radiusLapse V S other dother →
            RetardedBoundary (2*k) other dother out →
            (∀ r : ℝ, 2 < r → v r = other r ∧ dv r = dother r) ∧ q = out) ∧
          strainScale second k n*q = printedResponse second k n j.outgoing (u.outgoing/u.incoming) := by
  obtain ⟨a,j,u,incident,_,uin⟩ := global_strain_scattering_data n hn k hk ki
  refine ⟨a,j,u,⟨evenParentFromReference n hn k a hk ki j incident⟩,incident,uin,?_⟩
  intro second
  dsimp only
  let p := radialParticular second n k j.value j.jet
  let dp := exteriorParticularJet second n k j.value j.jet
  let pin := (parentAlpha k n)^2*endpointIncoming second k n
  let pout := j.outgoing^2*endpointOutgoing second k n
  let c := pin/u.incoming
  let v := fun r => p r-c*u.value r
  let dv := fun r => dp r-c*u.jet r
  let q := boundaryResponse second k n j.outgoing (u.outgoing/u.incoming)
  let V := rwPotential (2*k) (angularEigenvalue (2*n))
  let S := exteriorSource second n k j.value j.jet
  have wk : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wi : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  have pEq := admitted_exterior_forced_equation second n hn k hk ki j.value j.jet j.equation
  rw [← congrArg (rwPotential (2*k)) (angular_eigenvalue_double n)] at pEq
  have vEq : RadialEquation radiusLapse V S v dv := by
    simpa only [v,dv,p,dp,S,Pi.zero_apply,mul_zero,sub_zero] using
      radial_equation_sub_scaled c pEq u.equation
  have jInfinity := j.infinity
  rw [incident] at jInfinity
  have pInfinity : RadialModeLimits atTop (2*k) p dp pin pout :=
    admitted_particular_at_infinity second n hn k hk ki realTortoise j.value j.jet dp
      (parentAlpha k n) j.outgoing jInfinity j.equation pEq.value
  have modes := radial_mode_limits_sub_scaled c pInfinity u.infinity
  have cancelled := homogeneous_subtraction u.incoming u.outgoing pin pout uin
  have infinity : RadialModeLimits atTop (2*k) v dv 0 q := by
    have inZero : pin-c*u.incoming = 0 := cancelled.1
    have outValue : pout-c*u.outgoing = q := by
      rw [show pout-c*u.outgoing = pout-pin*(u.outgoing/u.incoming) from cancelled.2]
      simp only [q,boundaryResponse,pin,pout,mul_comm (j.outgoing^2)]
    rw [inZero,outValue] at modes
    exact modes
  obtain ⟨P,pa,pH⟩ := admitted_horizon_envelope second n hn k a hk ki j.value j.jet j.horizon j.equation.value
  obtain ⟨ua,uH⟩ := normalized_horizon_envelope (2*k) (angularEigenvalue (2*n)) 1 wi u.value u.horizon
  let H := fun z => P z-c*horizonEnvelope (2*k) (angularEigenvalue (2*n)) 1 z
  have analytic : AnalyticAt ℂ H 2 := pa.fun_sub ((analyticAt_const (v := c)).fun_mul ua)
  have vH : ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), v r = incomingCarrier (2*k) r*H (r : ℂ) := by
    filter_upwards [pH,uH] with r hp hu
    dsimp only [v,p,H]
    rw [hp,hu]
    unfold incomingCarrier
    ring
  have horizon := ingoing_analytic_mode_limits (2*k) wk wi realTortoise v dv H analytic
    (exterior_carrier_derivative (2*k)) vH vEq.value
  have boundary : RetardedBoundary (2*k) v dv q := ⟨⟨H 2,horizon⟩,infinity⟩
  exact ⟨vEq,⟨H,analytic,vH⟩,boundary,
    fun _ _ _ otherEq otherBC => retarded_solution_unique (2*k) (angularEigenvalue (2*n)) wk wi
      u uin vEq otherEq boundary otherBC,
    normalized_closed_response second n hn k j.outgoing (u.outgoing/u.incoming) ki⟩

#print axioms admitted_retarded_scattering

end
end SchwarzschildMixtures.Strain
