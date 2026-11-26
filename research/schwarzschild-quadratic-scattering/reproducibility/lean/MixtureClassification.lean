import MixtureSourceAlgebra
import AdmittedMixtures
import RegularizedOddSource
import OddCaseChecks
import RationalRowExclusion

/-! The two constructions and the pure-odd obstruction give one exact
classification of rational local particular fields on a fixed parent. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def publishedOdd (k ell : ℂ) : Row ℂᵣ :=
  oddForcing OddCase.multiplier OddCase.forcing k ell

/-- The published normalized forcing, recovered from the same three
source samples in the homogeneous quadratic family. -/
def publishedForcing (k ell a b : ℂ) : Row ℂᵣ :=
  interpolatedSource (alternativeRatio k ell) a b
    (admittedSource false k ell) (admittedSource true k ell) (publishedOdd k ell)

theorem published_forcing_from_components (k ell a b : ℂ) (ee eo : Row ℂᵣ)
    (hr : alternativeRatio k ell ≠ 1)
    (h₁ : quadraticSource ee eo (publishedOdd k ell) 1 1 = admittedSource false k ell)
    (h₂ : quadraticSource ee eo (publishedOdd k ell) 1 (alternativeRatio k ell) =
      admittedSource true k ell) :
    quadraticSource ee eo (publishedOdd k ell) a b = publishedForcing k ell a b := by
  rw [quadratic_source_factorization ee eo (publishedOdd k ell) _ a b hr, h₁, h₂, publishedForcing]

theorem rational_mixture_classification (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (a b : ℂ) :
    (∃ p : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k p =
      publishedForcing k n a b) ↔ b = a ∨ b = alternativeRatio k n*a := by
  have ho := odd_forcing_restored OddCase.multiplier n (by decide) hn k hk ki OddCase.field OddCase.forcing
    OddCase.odd_a_checked OddCase.odd_b_checked OddCase.odd_c_checked
  have exclude : ¬ ∃ p : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k p =
      archivedSource k n := by
    simpa only [Int.cast_natCast] using archived_rational_row_no_solution n hn k hk ki
  exact exact_roots_of_obstruction _ _ _ _ a b (admittedField false k n) (admittedField true k n)
    (oddShift OddCase.multiplier OddCase.field k n) (admittedSource false k n) (admittedSource true k n)
    (publishedOdd k n) (archivedSource k n) (admitted_field_solves false n hn k hk ki)
    (admitted_field_solves true n hn k hk ki) ho exclude

/-- For the same fixed nonzero parent, the two distinct lines are exactly
the mixtures with a rational local quadratic particular solution. -/
theorem meromorphic_mixture_classification (r : ℂ) (n : ℕ) (hn : 2 ≤ n)
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
        E.evaluateRow J (publishedForcing k n a b)) ↔
        b = a ∨ b = alternativeRatio k n*a := by
  dsimp only
  refine ⟨alternativeRatio_ne_one n hn k ki, fun a b => ?_⟩
  let E := MeromorphicRadial.differentialField r
  have hrow := rational_mixture_classification n hn k hk ki a b
  constructor
  · rintro ⟨p, hp⟩
    rw [E.evaluateRow_operator _ _ _ J parent p] at hp
    exact hrow.mp ⟨p, E.evaluateRow_injective n hn k hk ki J hJ parent hp⟩
  · intro root
    obtain ⟨p, hp⟩ := hrow.mpr root
    exact ⟨p, by rw [E.evaluateRow_operator _ _ _ J parent p, hp]⟩

#print axioms quadratic_source_factorization
#print axioms rational_mixture_classification
#print axioms meromorphic_mixture_classification

end
end SchwarzschildMixtures
