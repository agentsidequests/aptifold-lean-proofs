import MetricMixtureClassification
import MeromorphicRadialField

/-! Specialize the metric-source classification to the physical class
of rational quadratic fields on a fixed nonzero parent germ. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

theorem metric_meromorphic_classification (r : ℂ) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (J : MeromorphicRadial.At r) (hJ : J ≠ 0)
    (parent : (MeromorphicRadial.differentialField r).deriv ((MeromorphicRadial.differentialField r).deriv J) =
      (MeromorphicRadial.differentialField r).embed (parentTerm ((n:ℂ)*(n+1)) k)*J) :
    let E := MeromorphicRadial.differentialField r
    let hD := (2*(n:ℂ))*(2*(n:ℂ)+1)
    alternativeRatio k n ≠ 1 ∧ ∀ a b : ℂ,
      (∃ p : Row ℂᵣ,
        E.deriv (E.deriv (E.evaluateRow J p)) -
          E.embed (Cᵣ (4*k^2)+oddPotential hD)*E.evaluateRow J p =
        E.evaluateRow J (metricForcing k n a b)) ↔
        b = a ∨ b = alternativeRatio k n*a := by
  dsimp only
  refine ⟨alternativeRatio_ne_one n hn k ki, fun a b => ?_⟩
  let E := MeromorphicRadial.differentialField r
  have hrow := metric_mixture_classification n hn k hk ki a b
  constructor
  · rintro ⟨p, hp⟩
    rw [E.evaluateRow_operator _ _ _ J parent p] at hp
    exact hrow.mp ⟨p, E.evaluateRow_injective n hn k hk ki J hJ parent hp⟩
  · intro root
    obtain ⟨p, hp⟩ := hrow.mpr root
    exact ⟨p, by rw [E.evaluateRow_operator _ _ _ J parent p, hp]⟩

#print axioms metric_meromorphic_classification

end
end SchwarzschildMixtures
