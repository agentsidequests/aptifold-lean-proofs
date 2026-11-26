import RationalRowOperator

/-! Change of radial variable to reciprocal radius for the infinity equation. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

private theorem reciprocal_polynomial_injective :
    Function.Injective (Polynomial.aeval (R⁻¹) : ℂ[X] →ₐ[ℂ] ℂᵣ).toRingHom := by
  intro p q h
  apply sub_eq_zero.mp
  have hz : Polynomial.aeval R⁻¹ (p-q) = 0 := by
    rw [map_sub, show Polynomial.aeval R⁻¹ p = Polynomial.aeval R⁻¹ q from h, sub_self]
  rw [Polynomial.aeval_def, polynomial_reciprocal] at hz
  exact reverse_eq_zero.mp ((RatFunc.algebraMap_injective ℂ).eq_iff.mp
    (by simpa using ((div_eq_zero_iff).mp hz |>.resolve_right (pow_ne_zero _ RatFunc.X_ne_zero))))

def reciprocalHom : ℂᵣ →+* ℂᵣ := IsFractionRing.lift reciprocal_polynomial_injective

theorem reciprocalHom_polynomial (p : ℂ[X]) :
    reciprocalHom (ι p) = Polynomial.aeval R⁻¹ p :=
  IsFractionRing.lift_algebraMap reciprocal_polynomial_injective p

theorem reciprocal_eq_hom (u : ℂᵣ) : reciprocal u = reciprocalHom u := by
  calc
    reciprocal u =
      u.num.eval₂ (algebraMap ℂ ℂᵣ) R⁻¹ / u.denom.eval₂ (algebraMap ℂ ℂᵣ) R⁻¹ := rfl
    _ = reciprocalHom (ι u.num / ι u.denom) := by
      simp only [map_div₀, reciprocalHom_polynomial, Polynomial.aeval_def]
    _ = _ := by rw [RatFunc.num_div_denom]

theorem reciprocalRow_eq_hom (u : Row ℂᵣ) : reciprocalRow u = mapRow reciprocalHom u := by
  simp [reciprocalRow, reciprocal_eq_hom, mapRow]

@[simp] theorem reciprocalHom_radius : reciprocalHom R = R⁻¹ := by
  simpa only [RatFunc.algebraMap_X, Polynomial.aeval_X] using reciprocalHom_polynomial (X : ℂ[X])

@[simp] theorem reciprocalHom_constant (a : ℂ) : reciprocalHom (Cᵣ a) = Cᵣ a := by
  simpa only [RatFunc.algebraMap_C, Polynomial.aeval_C, RatFunc.algebraMap_eq_C] using reciprocalHom_polynomial (C a)

theorem derivative_reciprocal (u : ℂᵣ) :
    δ (reciprocalHom u) = (-1/R^2) * reciprocalHom (δ u) := by
  refine RatFunc.induction_on
    (P := fun x => δ (reciprocalHom x) = (-1/R^2) * reciprocalHom (δ x)) u ?_
  intro p q hq
  rw [rationalDerivative_fraction p q hq]
  simp only [map_div₀, map_pow, reciprocalHom_polynomial, rationalDerivative_div,
    rationalDerivative_aeval, rationalDerivative_inv, rationalDerivative_radius, map_mul, map_sub]
  ring

private theorem reciprocal_radial_factor : reciprocalHom radialFactor = ι (1-2*X) := by
  simp only [radialFactor, map_div₀, map_sub, reciprocalHom_radius, map_ofNat, map_one, map_mul,
    RatFunc.algebraMap_X]
  field_simp [RatFunc.X_ne_zero]

private theorem reciprocal_oddPotential (h : ℂ) : reciprocalHom (oddPotential h) = ι (infinityPotential h) := by
  simp only [oddPotential, map_mul, reciprocal_radial_factor, map_sub, map_div₀, map_pow,
    reciprocalHom_constant, reciprocalHom_radius, map_ofNat, infinityPotential,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [RatFunc.X_ne_zero]

def localEulerRow (a : ℂ) (u : Row ℂᵣ) : Row ℂᵣ := mapRow (euler a) u

theorem localEulerRow_correct (a : ℂ) (u : Row ℂᵣ) :
    localEulerRow a u = scale (ι (localCoordinate a)) (rationalRowDerivative u) := rfl

def infinityStep (h k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  plus (scale (ι infinityVelocity) (localEulerRow 0 u)) (jet (ι (infinityJetA h k)) 0 1 u)

def infinityOperator (h hD k : ℂ) (u : Row ℂᵣ) : Row ℂᵣ :=
  minus (infinityStep h k (infinityStep h k u)) (scale (ι (infinityDaughter hD k)) u)

private theorem reciprocal_derivative_row (u : Row ℂᵣ) :
    mapRow reciprocalHom (rationalRowDerivative u) =
      scale (-R^2) (rationalRowDerivative (mapRow reciprocalHom u)) := by
  simp only [mapRow, rationalRowDerivative, scale, derivative_reciprocal]
  apply Prod.ext
  · field_simp [RatFunc.X_ne_zero]
  · apply Prod.ext <;> field_simp [RatFunc.X_ne_zero]

private theorem reciprocal_step_correct (h k : ℂ) (u : Row ℂᵣ) :
    mapRow reciprocalHom (unscaledStep h k u) = infinityStep h k (mapRow reciprocalHom u) := by
  simp only [unscaledStep, infinityStep, mapRow_plus, mapRow_scale, mapRow_jet,
    reciprocal_radial_factor, reciprocal_derivative_row, map_add, reciprocalHom_constant,
    reciprocal_oddPotential, map_zero, map_one, infinityJetA, RatFunc.algebraMap_C,
    localEulerRow_correct, infinityVelocity, localCoordinate, map_mul, map_neg, map_sub,
    map_ofNat, map_one, map_zero, RatFunc.algebraMap_X, RatFunc.algebraMap_C, sub_zero, scale_scale]
  congr 1
  ring

theorem reciprocal_operator_correct (h hD k : ℂ) (u : Row ℂᵣ) :
    reciprocalRow (unscaledRow (rationalOperator h hD k u)) =
      infinityOperator h hD k (reciprocalRow (unscaledRow u)) := by
  simp only [reciprocalRow_eq_hom, unscaled_operator_correct, unscaledOperator, mapRow_minus,
    reciprocal_step_correct, mapRow_scale, map_add, reciprocalHom_constant, reciprocal_oddPotential,
    infinityOperator, infinityDaughter, RatFunc.algebraMap_C]

#print axioms derivative_reciprocal
#print axioms reciprocal_operator_correct

end

end SchwarzschildLaurent
