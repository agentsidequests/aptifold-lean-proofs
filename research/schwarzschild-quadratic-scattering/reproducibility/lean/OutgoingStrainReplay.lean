import OutgoingMixtureHorizon
import OutgoingStrainNormalization

/-! The complex outgoing response of both admitted mixtures.
The global linear waves and their infinity mode limits are inputs. -/
namespace SchwarzschildMixtures.Strain

open Filter MeasureTheory ComplexConjugate
open scoped Topology Interval
open SchwarzschildLaurent.Outgoing SchwarzschildMixtures.OutgoingData

noncomputable section

private theorem daughter_potential_real (n : ℕ) (k : ℂ) (ki : k.re = 0) (r : ℝ) :
    conj (rwPotential (2*k) (2*(n : ℂ)*(2*n+1)) r) =
      rwPotential (2*k) (2*(n : ℂ)*(2*n+1)) r := by
  have wIm : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  have real := rw_potential_is_real (2*k) wIm (2*(n : ℝ)*(2*n+1)) r
  push_cast at real
  exact real

/-- The improper retarded integral gives the printed complex strain for
either actual rational particular field. The incoming normalization of
the homogeneous daughter is nonzero by conserved flux. -/
theorem admitted_outgoing_strain (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k rp ain aout parentScale transmission : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (transmitted : transmission ≠ 0) (j dj u du dp S : ℝ → ℂ)
    (jEq : RadialEquation radiusLapse (rwPotential k ((n : ℂ)*(n+1))) 0 j dj)
    (uEq : RadialEquation radiusLapse (rwPotential (2*k) (2*(n : ℂ)*(2*n+1))) 0 u du)
    (pEq : RadialEquation radiusLapse (rwPotential (2*k) (2*(n : ℂ)*(2*n+1))) S
      (radialParticular second n k j dj) dp)
    (jHorizon : j =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch k ((n : ℂ)*(n+1)) parentScale)
    (uHorizon : u =ᶠ[𝓝[>] (2 : ℝ)] horizonBranch (2*k) (2*(n : ℂ)*(2*n+1)) transmission)
    (jInfinity : ModeLimits atTop k (fun r => phase (-k) (realTortoise r))
      (fun r => phase k (realTortoise r)) j dj (parentAlpha k n) rp)
    (uInfinity : ModeLimits atTop (2*k) (fun r => phase (-(2*k)) (realTortoise r))
      (fun r => phase (2*k) (realTortoise r)) u du ain aout)
    (finiteIntegrable : ∀ a b : ℝ, 2 < a → 2 < b →
      IntervalIntegrable (fun r => u r*S r/radiusLapse r) volume a b) :
    ain ≠ 0 ∧
    Tendsto (fun ab : ℝ × ℝ =>
      strainScale second k n * ((∫ r in ab.1..ab.2, u r*S r/radiusLapse r)/(4*k*ain)))
      ((𝓝[>] (2 : ℝ)) ×ˢ atTop) (𝓝 (printedResponse second k n rp (aout/ain))) := by
  have wNonzero : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have wImaginary : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  have uModes := normalized_horizon_modes (2*k) _ transmission wNonzero wImaginary u du uHorizon uEq.value
  have flux := flux_balance (2*k) wNonzero wImaginary realTortoise radiusLapse _ u du
    lapse_is_real (daughter_potential_real n k ki) uEq ain aout transmission uInfinity uModes
  have hIn := nonzero_incident_amplitude flux transmitted
  have hZero := admitted_particular_horizon_current second n hn k parentScale transmission hk ki
    j dj u du dp jHorizon uHorizon jEq.value uEq.value pEq.value
  have particular := admitted_particular_at_infinity second n hn k hk ki realTortoise j dj dp
    (parentAlpha k n) rp jInfinity jEq pEq.value
  let b_in := (parentAlpha k n)^2*endpointIncoming second k n
  let b_out := rp^2*endpointOutgoing second k n
  have wLimit := current_of_mode_limits atTop (2*k) wNonzero _ _ u du _ dp
    (fun r => opposite_phases (2*k) (realTortoise r)) ain aout b_in b_out uInfinity particular
  have impulse := green_integral_from_endpoint_limits radiusLapse _ S u du _ dp _ uEq pEq
    finiteIntegrable hZero wLimit
  have normalized := (impulse.div_const (4*k*ain)).const_mul (strainScale second k n)
  have expected : strainScale second k n * ((2*(2*k)*(ain*b_out-aout*b_in))/(4*k*ain)) =
      printedResponse second k n rp (aout/ain) := by
    rw [normalized_green_response k ain aout b_in b_out hk hIn, ← normalized_closed_response second n hn k rp _ ki]
    unfold boundaryResponse b_in b_out
    ring
  rw [expected] at normalized
  exact ⟨hIn,normalized⟩

#print axioms admitted_outgoing_strain

end
end SchwarzschildMixtures.Strain
