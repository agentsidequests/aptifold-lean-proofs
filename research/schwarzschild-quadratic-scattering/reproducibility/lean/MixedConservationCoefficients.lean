import MixedConservationFormulaEvaluation
import MixedConservationWitness
import PureOddPhysicalDomain

/-! Bind the exact reduction to the mixed conservation program, then
transport its vanishing coefficients to a compatible differential field. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open SchwarzschildLaurent SchwarzschildMixtures.ExactRational
open SchwarzschildMixtures (Expr)
open SchwarzschildMixtures.MixedConservationWitness

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

attribute [local irreducible] conservationCoefficients

private theorem reduced_zero {f : Formula} {p : Fraction} (h : Reduced f p)
    (num : Expr.Check p.num (.constant 0)) (k ell : ℂ) (hz : DivisorsNonzero k ell) :
    f.value k ell = 0 := by
  rw [(h.sound k ell hz).1]
  simp [Fraction.value, Expr.value_eq_of_check _ _ num, Expr.value_constant]

theorem conservation_coefficients_zero (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    mapRow (Formula.value k n) conservationCoefficients = (0,0,0) := by
  have hz := SchwarzschildMixtures.PureOddProgram.physical_divisors_nonzero n hn k ki
  exact Prod.ext (reduced_zero reducedA numeratorA k n hz)
    (Prod.ext (reduced_zero reducedB numeratorB k n hz) (reduced_zero reducedC numeratorC k n hz))

variable {K : Type} [Field K]

private theorem interpret_extension (embed : ℂᵣ →+* K) (d : K → K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u))
    (k ell : ℂ) (f : Formula) :
    Formula.interpret d (embed R) (embed (Cᵣ k)) (embed (Cᵣ ell)) f = embed (f.value k ell) := by
  induction f <;>
    simp only [Formula.interpret, Formula.value, map_intCast, map_add, map_mul, map_div₀,
      map_neg, *]

theorem conservation_rows_zero (embed : ℂᵣ →+* K) (d : K → K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    conservationRows (fun q => (q : K)) d (embed R) (embed (Cᵣ k)) (embed (Cᵣ (n:ℂ))) =
      (0,0,0) := by
  rw [← conservation_program_value]
  have h := congrArg (mapRow embed) (conservation_coefficients_zero n hn k ki)
  simpa only [mapRow, map_zero, interpret_extension embed d compatible] using h

#print axioms conservation_coefficients_zero
#print axioms conservation_rows_zero

end
end SchwarzschildEinstein.PureOdd.Mixed
