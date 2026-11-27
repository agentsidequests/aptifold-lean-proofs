import MetricMeromorphicClassification
import RegularizationBridge
import RationalLocalUniqueness
import AdmittedFutureHorizon
import VacuumSeries
import ParityMasterProjection
import QuadraticScatteringReconstruction

/-! Review entry point for Theorem 1 of the Schwarzschild scattering preprint.
The statement below uses its positive-frequency and projective coordinates. -/
namespace AptifoldReview

open SchwarzschildLaurent SchwarzschildMixtures

noncomputable section

def frequencyParameter (ω : ℝ) : ℂ := Complex.I * (ω : ℂ)

/-- On a fixed nonzero parent germ, the regularized projected equation has a
rational quadratic particular field exactly on the two distinct incident lines.
The top daughter has multipole `2 * n` and frequency `2 * ω`. -/
theorem positive_frequency_classification (r : ℂ) (n : ℕ) (hn : 2 ≤ n)
    (ω : ℝ) (hω : 0 < ω) (J : MeromorphicRadial.At r) (hJ : J ≠ 0)
    (parent : (MeromorphicRadial.differentialField r).deriv
        ((MeromorphicRadial.differentialField r).deriv J) =
      (MeromorphicRadial.differentialField r).embed
        (parentTerm ((n : ℂ) * (n + 1)) (frequencyParameter ω)) * J) :
    let E := MeromorphicRadial.differentialField r
    let k := frequencyParameter ω
    let ρ := alternativeRatio k n
    let hD := (2 * (n : ℂ)) * (2 * (n : ℂ) + 1)
    ρ ≠ 1 ∧ ∀ a b : ℂ, (a, b) ≠ (0, 0) →
      ((∃ p : Row (RatFunc ℂ),
          E.deriv (E.deriv (E.evaluateRow J p)) -
            E.embed (RatFunc.C (4 * k^2) + oddPotential hD) * E.evaluateRow J p =
          E.evaluateRow J (publishedForcing k n a b)) ↔
        ∃ s : ℂ, s ≠ 0 ∧ a = s ∧ (b = s ∨ b = ρ * s)) := by
  have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have hk : frequencyParameter ω ≠ 0 := mul_ne_zero Complex.I_ne_zero hωc
  have ki : (frequencyParameter ω).re = 0 := by
    simp [frequencyParameter, Complex.mul_re]
  obtain ⟨distinct, classify⟩ := meromorphic_mixture_classification r n hn
    (frequencyParameter ω) hk ki J hJ parent
  refine ⟨distinct, fun a b hpair => (classify a b).trans ?_⟩
  constructor
  · intro h
    have ha : a ≠ 0 := by
      intro azero
      have bzero : b = 0 := by
        rcases h with h | h <;> simpa [azero] using h
      exact hpair (Prod.ext azero bzero)
    exact ⟨a, ha, rfl, h⟩
  · rintro ⟨s, _, rfl, h⟩
    exact h

#print axioms positive_frequency_classification

set_option maxHeartbeats 800000 in
/-- The second line has the frequency-independent master ratio printed in
Theorem 1. The first line uses `ρ = 1` in the same factor `-I * ρ * α`. -/
theorem second_incident_ratio (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    -Complex.I * alternativeRatio k n * ((gamma n + k) / (gamma n - k)) =
      -Complex.I * ((9 * (n : ℂ)^2 + n - 4) / (7 * (n : ℂ)^2 - n)) := by
  have hgplus := gamma_add_frequency n hn k ki
  have hgminus : gamma (n : ℂ) - k ≠ 0 := by
    simpa only [sub_eq_add_neg] using gamma_add_frequency n hn (-k) (by simp [ki])
  have hgap : daughterGamma (n : ℂ) - gamma (n : ℂ) ≠ 0 := by
    intro h
    exact (gap_positive n hn).ne' (by simp [h])
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdenR : (7 * (n : ℝ)^2 - n) ≠ 0 := by
    have hp : (0 : ℝ) < (n : ℝ) * (7 * (n : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    apply ne_of_gt
    nlinarith only [hp]
  have hden : (7 * (n : ℂ)^2 - n) ≠ 0 := by exact_mod_cast hdenR
  have hcancel : alternativeRatio k n * ((gamma n + k) / (gamma n - k)) =
      (daughterGamma n + gamma n) / (daughterGamma n - gamma n) := by
    unfold alternativeRatio
    field_simp [hgplus, hgminus, hgap]
  have hratio : (daughterGamma n + gamma n) / (daughterGamma n - gamma n) =
      (9 * (n : ℂ)^2 + n - 4) / (7 * (n : ℂ)^2 - n) := by
    apply (div_eq_div_iff hgap hden).2
    unfold daughterGamma gamma
    ring
  rw [mul_assoc, hcancel, hratio]

#print axioms second_incident_ratio

end
end AptifoldReview
