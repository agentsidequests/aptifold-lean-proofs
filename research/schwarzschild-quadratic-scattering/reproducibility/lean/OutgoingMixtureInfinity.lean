import OutgoingMixtureLimits
import OutgoingRadiusLimits

/-! Assemble the infinity limits for the actual two particular fields,
including their jets in Schwarzschild radial coordinates. -/
namespace SchwarzschildMixtures.Strain

open Polynomial SchwarzschildLaurent.Outgoing SchwarzschildMixtures.OutgoingData Filter
open scoped Topology

noncomputable section

def radialParticular (second : Bool) (n : ℕ) (k : ℂ) (j dj : ℝ → ℂ) (r : ℝ) : ℂ :=
  quadraticValue (effectiveFieldCoefficients second k n (r : ℂ)) (j r) (dj r)

private theorem polynomial_analytic (a : ℂ) (p : ℂ[X]) : AnalyticAt ℂ p.eval a := by
  induction p using Polynomial.induction_on' with
  | add b c hb hc => simpa only [eval_add] using hb.fun_add hc
  | monomial n c =>
    have power : AnalyticAt ℂ (fun z : ℂ => z^n) a := by fun_prop
    simpa only [eval_monomial] using (analyticAt_const (v := c)).fun_mul power

private theorem actual_row_limits (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    let A := reciprocalCoefficients second k n
    CoefficientLimits radiusLapse (reciprocalValue A) (reciprocalJet A) (A 0) ∧
      ∀ᶠ r : ℝ in atTop, effectiveFieldCoefficients second k n (r : ℂ) = reciprocalValue A r := by
  let d := reflectedDenominator (reciprocalScalar second k n) n
  have da : AnalyticAt ℂ d 0 := by
    change AnalyticAt ℂ (fun t => reflectedDenominator (reciprocalScalar second k n) n t) 0
    unfold reflectedDenominator
    fun_prop
  have d0 : d 0 ≠ 0 := reciprocal_at_zero_nonzero second n hn k hk ki
  have quo (p : ℂ[X]) : AnalyticAt ℂ (fun t => p.eval t/d t) 0 :=
    (polynomial_analytic 0 p).fun_div da d0
  refine ⟨reciprocal_row_limits _ (quo _) (quo _) (quo _),?_⟩
  filter_upwards [eventually_gt_atTop (2:ℝ),
    inverse_radius_tends_to_zero.eventually (da.continuousAt.eventually_ne d0)] with r hr den
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  exact effective_row_equation second k n (r : ℂ) nz den

theorem admitted_particular_at_infinity (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (x : ℝ → ℝ) (j dj dP : ℝ → ℂ)
    (ain aout : ℂ)
    (parent : ModeLimits atTop k (fun r => phase (-k) (x r)) (fun r => phase k (x r)) j dj ain aout)
    (parentEq : RadialEquation radiusLapse (rwPotential k ((n : ℂ)*(n+1))) 0 j dj)
    (pJet : ∀ r, 2 < r → HasDerivAt (radialParticular second n k j dj) (dP r/radiusLapse r) r) :
    ModeLimits atTop (2*k) (fun r => phase (-(2*k)) (x r)) (fun r => phase (2*k) (x r))
      (radialParticular second n k j dj) dP
      (ain^2*endpointIncoming second k n) (aout^2*endpointOutgoing second k n) := by
  obtain ⟨c,eq⟩ := actual_row_limits second n hn k hk ki
  have value : ∀ᶠ r : ℝ in atTop, radialParticular second n k j dj r =
      quadraticValue (reciprocalValue (reciprocalCoefficients second k n) r) (j r) (dj r) := by
    filter_upwards [eq] with r row
    rw [radialParticular,row]
  have limits := quadratic_mode_limits k hk _ _ (fun r => opposite_phases k (x r))
    (fun r => phase_norm (-k) (by simp [ki]) (x r)) (fun r => phase_norm k ki (x r)) _ _ j dj _ dP
    _ _ _ ain aout parent parentEq (potential_tends_to_frequency k _)
    ((eventually_gt_atTop (2:ℝ)).mono fun _ h => exterior_lapse_nonzero h)
    c (mixed_endpoint_zero second k n) value pJet
  obtain ⟨out,inc⟩ := signed_endpoint_coefficients second n hn k hk ki
  have hₒ : quadraticValue (reciprocalCoefficients second k n 0) 1 k = endpointOutgoing second k n := by
    simpa [quadraticValue,signedWeight,mul_comm] using out
  have hᵢ : quadraticValue (reciprocalCoefficients second k n 0) 1 (-k) = endpointIncoming second k n := by
    simpa [quadraticValue,signedWeight,mul_comm] using inc
  have sign : -(2*k) = 2*(-k) := by ring
  simpa only [sign,phase_double,hₒ,hᵢ] using limits

#print axioms admitted_particular_at_infinity

end
end SchwarzschildMixtures.Strain
