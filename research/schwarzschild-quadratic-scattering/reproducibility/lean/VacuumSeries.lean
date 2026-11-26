import VacuumJetGeometry

/-! The two lower Ricci coefficients used by the quadratic Einstein
expansion are exactly the background and first-order jet calculations. -/
namespace SchwarzschildEinstein.PureOdd.Vacuum

open PowerSeries
open scoped BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [Field A]

private theorem mul_coeff_zero (p q : A⟦X⟧) :
    coeff 0 (p*q) = coeff 0 p*coeff 0 q := by
  simp [coeff_zero_eq_constantCoeff_apply]

private theorem mul_coeff_one (p q : A⟦X⟧) :
    coeff 1 (p*q) = coeff 0 p*coeff 1 q+coeff 1 p*coeff 0 q := by
  rw [PowerSeries.coeff_one_mul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
  ring

theorem ricci_lower_coefficients [DecidableEq ι] (d : ι → A → A)
    (g B : Tensor ι A⟦X⟧) (inverse : B*g = 1)
    (right : tensorCoeff 0 g * tensorCoeff 0 B = 1) :
    let Γ := christoffel (C (1/2)) (seriesPartial d) B g
    let Ric := ricci (seriesPartial d) Γ
    tensorCoeff 0 Ric = ricci d (christoffel (1/2) d (tensorCoeff 0 B) (tensorCoeff 0 g)) ∧
      tensorCoeff 1 Ric = linearRicci d (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 1 g) := by
  let Γ := christoffel (C (1/2)) (seriesPartial d) B g
  have h₀ : connectionCoeff 0 Γ = christoffel (1/2) d (tensorCoeff 0 B) (tensorCoeff 0 g) := by
    funext a b c
    simp only [Γ, connectionCoeff, christoffel, metricDerivative, tensorCoeff,
      PowerSeries.coeff_C_mul, map_sum, mul_coeff_zero, map_add, map_sub, coeff_partial]
  have h₁ : connectionCoeff 1 Γ = linearConnection d (tensorCoeff 0 g) (tensorCoeff 0 B) (tensorCoeff 1 g) := by
    have B₁ := (inverse_coefficients g B inverse right).1
    unfold linearConnection
    rw [← B₁]
    funext a b c
    simp only [Γ, connectionCoeff, christoffel, metricDerivative, tensorCoeff,
      PowerSeries.coeff_C_mul, map_sum, mul_coeff_one, map_add, map_sub, coeff_partial,
      Pi.add_apply, Finset.sum_add_distrib, mul_add]
  have zero : tensorCoeff 0 (ricci (seriesPartial d) Γ) = ricci d (connectionCoeff 0 Γ) := by
    ext a b
    simp only [tensorCoeff, ricci, Matrix.add_apply, connectionDivergence, connectionProduct,
      connectionCoeff, map_add, map_sub, map_sum, coeff_partial, mul_coeff_zero]
  have one : tensorCoeff 1 (ricci (seriesPartial d) Γ) =
      connectionDivergence d (connectionCoeff 1 Γ) +
        (connectionProduct (connectionCoeff 0 Γ) (connectionCoeff 1 Γ) +
         connectionProduct (connectionCoeff 1 Γ) (connectionCoeff 0 Γ)) := by
    ext a b
    simp only [tensorCoeff, ricci, Matrix.add_apply, connectionDivergence, connectionProduct,
      connectionCoeff, map_add, map_sub, map_sum, coeff_partial, mul_coeff_one]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  change tensorCoeff 0 (ricci (seriesPartial d) Γ) = _ ∧ tensorCoeff 1 (ricci (seriesPartial d) Γ) = _
  exact ⟨by rw [zero, h₀], by rw [one, h₀, h₁, linearRicci]⟩

theorem lower_vacuum_from_jets {K : Type*} [Field K] [Algebra ℚ K]
    (d : Axis → Derivation ℚ K K) (g B : Tensor Axis K⟦X⟧) (inverse : B*g = 1)
    (right : tensorCoeff 0 g * tensorCoeff 0 B = 1)
    (bg : backgroundJetRicci (secondMetric d (tensorCoeff 0 g)) (firstMetric d (tensorCoeff 0 B)) = 0)
    (parent : linearJetRicci (secondMetric d (tensorCoeff 0 g)) (firstMetric d (tensorCoeff 0 B))
      (secondMetric d (tensorCoeff 1 g)) = 0) :
    let d' : Axis → K → K := fun i => d i
    let Ric := ricci (seriesPartial d') (christoffel (C (1/2)) (seriesPartial d') B g)
    tensorCoeff 0 Ric = 0 ∧ tensorCoeff 1 Ric = 0 := by
  obtain ⟨h₀,h₁⟩ := ricci_lower_coefficients (fun i => d i) g B inverse right
  rw [background_ricci_of_jets] at bg
  rw [linear_ricci_of_jets] at parent
  exact ⟨h₀.trans bg, h₁.trans parent⟩

#print axioms ricci_lower_coefficients
#print axioms lower_vacuum_from_jets

end
end SchwarzschildEinstein.PureOdd.Vacuum
