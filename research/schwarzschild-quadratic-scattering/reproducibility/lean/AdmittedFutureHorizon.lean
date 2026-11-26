import AdmittedHorizon
import HorizonIngoingParent

/-! The regularized scalar solutions extend analytically in ingoing
Eddington–Finkelstein coordinates \((v,r)\) across \(r=2\). -/
namespace SchwarzschildMixtures

open Filter SchwarzschildLaurent Horizon
open scoped Topology

noncomputable section

def realTortoise (r : ℝ) : ℝ := r+2*Real.log (r/2-1)

/-- The regularized daughter with its time dependence in Schwarzschild
coordinates. Its radial input is the phase-restored parent wave. -/
def exteriorDaughter (second : Bool) (n : ℕ) (k : ℂ) (J : ℂ → ℂ) (t r : ℝ) : ℂ :=
  Complex.exp (-(2*k)*(t : ℂ)) *
    evaluateEnvelopeAt (admittedField second k n) J (fun z => z^2*tortoiseDifferential J z) r

def ingoingDaughter (k : ℂ) (G : ℂ → ℂ) (vr : ℂ × ℂ) : ℂ :=
  Complex.exp (-(2*k)*vr.1)*G vr.2

private theorem exterior_radius_tendsto :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 (2 : ℂ)) := by
  have coe := (Complex.continuous_ofReal.continuousAt (x := (2:ℝ))).tendsto
  simpa only [Complex.ofReal_ofNat] using coe.mono_left nhdsWithin_le_nhds

private theorem exterior_radius_tendsto_puncture :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ exterior_radius_tendsto
  filter_upwards [self_mem_nhdsWithin] with r hr
  change (r : ℂ) ≠ 2
  exact_mod_cast (ne_of_gt (show 2 < r from hr))

private theorem ingoing_daughter_analytic (k : ℂ) {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 2)
    (v : ℂ) : AnalyticAt ℂ (ingoingDaughter k G) (v,2) := by
  have snd : AnalyticAt ℂ (fun vr : ℂ × ℂ => vr.2) (v,2) := analyticAt_snd
  have composed : AnalyticAt ℂ (fun vr : ℂ × ℂ => G vr.2) (v,2) := hG.fun_comp_of_eq snd rfl
  have fst : AnalyticAt ℂ (fun vr : ℂ × ℂ => vr.1) (v,2) := analyticAt_fst
  have exponent := (analyticAt_const (v := -(2*k))).fun_mul fst
  unfold ingoingDaughter
  exact (exponent.cexp).fun_mul composed

/-- Extend either checked field for any analytic ingoing parent envelope.
The equality uses the actual rational rows and the manuscript's tortoise
coordinate. The extension is analytic in advanced time and areal radius. -/
theorem admitted_future_horizon_of_envelope (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (H : ℂ → ℂ) (hH : AnalyticAt ℂ H 2) :
    ∃ G : ℂ → ℂ, (∀ v : ℂ, AnalyticAt ℂ (ingoingDaughter k G) (v,2)) ∧
      ∀ᶠ r in 𝓝[>] (2 : ℝ), ∀ t : ℝ,
        exteriorDaughter second n k (ingoingWave k H) t r =
          ingoingDaughter k G (↑(t+realTortoise r),↑r) := by
  obtain ⟨G,hG,germ_eq⟩ := admitted_horizon_extension second n hn k hk ki H hH
  let row := admittedField second k n
  let Z := envelopeJet k H
  have eq := exterior_radius_tendsto_puncture.eventually
    (extension_agrees_with_evaluation row hH (envelope_jet_analytic k hH) hG germ_eq)
  refine ⟨G,ingoing_daughter_analytic k hG,?_⟩
  filter_upwards [eq,exterior_radius_tendsto.eventually hH.eventually_analyticAt,
    self_mem_nhdsWithin] with r extension hrH hr t
  have pos : 2 < r := hr
  let z : ℂ := r
  have hnz : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < r by linarith))
  have jet : z^2*tortoiseDifferential (ingoingWave k H) z = ingoingCarrier k z*Z z := by
    rw [ingoing_wave_first_derivative k (exterior_log_argument r pos) hnz hrH.differentiableAt]
    dsimp only [radialLapse, Z, envelopeJet, z]
    field_simp [hnz]
  have quad : evaluateEnvelopeAt row (ingoingWave k H)
      (fun x => x^2*tortoiseDifferential (ingoingWave k H) x) z =
        (ingoingCarrier k z)^2*G z := by
    rw [← extension]
    change _ = (ingoingCarrier k z)^2*evaluateEnvelopeAt row H Z z
    dsimp only [evaluateEnvelopeAt]
    rw [jet]
    unfold ingoingWave
    ring
  change Complex.exp (-(2*k)*(t : ℂ))*evaluateEnvelopeAt row (ingoingWave k H)
      (fun x => x^2*tortoiseDifferential (ingoingWave k H) x) z =
    Complex.exp (-(2*k)*↑(t+realTortoise r))*G z
  rw [quad, ← mul_assoc, pow_two]
  unfold ingoingCarrier
  rw [tortoise_real_exterior r pos, ← Complex.exp_add, ← Complex.exp_add]
  unfold realTortoise
  congr 2
  simp only [Complex.ofReal_add]
  ring

/-- The normalized Taylor solution, scaled by an arbitrary parent
amplitude, is a Regge–Wheeler wave on the exterior near the horizon. -/
theorem convergent_ingoing_parent_is_rw_wave (n : ℕ) (k a : ℂ) (ki : k.re = 0) :
    let L := (n : ℂ)*(n+1)
    let J := ingoingWave k (fun z => a*normalizedEnvelope k L z)
    ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ),
      tortoiseDifferential (tortoiseDifferential J) (r : ℂ) =
        (k^2+radialLapse (r : ℂ)*(L/(r : ℂ)^2-6/(r : ℂ)^3))*J (r : ℂ) := by
  let L := (n : ℂ)*(n+1)
  let H := fun z => a*normalizedEnvelope k L z
  have ha : AnalyticAt ℂ H 2 := (analyticAt_const (v := a)).fun_mul (normalized_envelope_analytic k L ki)
  dsimp only
  filter_upwards [self_mem_nhdsWithin,exterior_radius_tendsto.eventually ha.eventually_analyticAt,
    exterior_radius_tendsto.eventually (scaled_envelope_residual k L a ki)] with r hr hh eq
  have pos : 2 < r := hr
  have hnz : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < r by linarith))
  exact ingoing_wave_from_envelope k L (exterior_log_argument r pos) hnz hh eq

/-- The first-order correction to \(Z/J\) on the actual ingoing
solution. Its value checks the distinction between a simple pole and
a higher-order pole in the daughter coefficients. -/
theorem ingoing_jet_ratio_expansion (k L : ℂ) (ki : k.re = 0) :
    let H := normalizedEnvelope k L
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 2 ∧ B 2 = (L-3)/(1-4*k)-4*k ∧
      ∀ᶠ r in 𝓝 (2 : ℂ), envelopeJet k H r / H r = -4*k+(r-2)*B r := by
  let H := normalizedEnvelope k L
  let B := fun r => r*(deriv H r / H r)-k*(r+2)
  have hH : AnalyticAt ℂ H 2 := normalized_envelope_analytic k L ki
  have at_horizon : H 2 = 1 := normalized_envelope_horizon k L
  have nonzero : H 2 ≠ 0 := by rw [at_horizon]; exact one_ne_zero
  have quotient := hH.deriv.fun_div hH nonzero
  have eq : deriv H 2 = (L-3)/(2*(1-4*k)) := normalized_envelope_radial_derivative k L ki
  refine ⟨B,by fun_prop,?_,?_⟩
  · have hk : 1-4*k ≠ 0 := by
      intro zero
      exact horizon_leading_ne_zero k ki 0 (by simp [horizonLeading,zero])
    dsimp only [B]
    rw [at_horizon, div_one, eq]
    field_simp [hk]
    ring
  · filter_upwards [hH.continuousAt.eventually_ne nonzero] with r nz
    have nonzeroAt : normalizedEnvelope k L r ≠ 0 := nz
    dsimp only [envelopeJet,B,H]
    field_simp [nonzeroAt]
    ring

/-- Both admitted fields extend across the future horizon on the
convergent ingoing Regge–Wheeler branch, at any parent normalization. -/
theorem admitted_future_horizon_extension (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k a : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    let H := fun z => a*normalizedEnvelope k ((n : ℂ)*(n+1)) z
    ∃ G : ℂ → ℂ, (∀ v : ℂ, AnalyticAt ℂ (ingoingDaughter k G) (v,2)) ∧
      ∀ᶠ r in 𝓝[>] (2 : ℝ), ∀ t : ℝ,
        exteriorDaughter second n k (ingoingWave k H) t r =
          ingoingDaughter k G (↑(t+realTortoise r),↑r) := by
  exact admitted_future_horizon_of_envelope second n hn k hk ki _
    ((analyticAt_const (v := a)).fun_mul (normalized_envelope_analytic k ((n : ℂ)*(n+1)) ki))

#print axioms admitted_future_horizon_of_envelope
#print axioms convergent_ingoing_parent_is_rw_wave
#print axioms ingoing_jet_ratio_expansion
#print axioms admitted_future_horizon_extension

end
end SchwarzschildMixtures
