import RationalRowExclusion

/-! Algebraic reduction of a quadratic family to its two normalized
solutions and the obstruction at the pure-odd coefficient. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def quadraticSource (ee eo oo : Row ℂᵣ) (a b : ℂ) : Row ℂᵣ :=
  plus (scale (Cᵣ (a^2)) ee) (plus (scale (Cᵣ (a*b)) eo) (scale (Cᵣ (b^2)) oo))

def oddWeight (rho a b : ℂ) : ℂ := (b-a)*(b-rho*a)

/-- A homogeneous quadratic source is determined by its two normalized
mixture values and its pure-odd coefficient. -/
def interpolatedSource (rho a b : ℂ) (first second odd : Row ℂᵣ) : Row ℂᵣ :=
  plus (scale (Cᵣ (a^2)) first)
    (plus (scale (Cᵣ (a*(b-a)/(rho-1))) (minus second first))
      (scale (Cᵣ (oddWeight rho a b)) odd))

theorem quadratic_source_factorization (ee eo oo : Row ℂᵣ) (rho a b : ℂ) (hr : rho ≠ 1) :
    quadraticSource ee eo oo a b =
      interpolatedSource rho a b (quadraticSource ee eo oo 1 1) (quadraticSource ee eo oo 1 rho) oo := by
  have hden : Cᵣ rho - 1 ≠ 0 := sub_ne_zero.mpr
    (by simpa only [map_one] using RatFunc.C_injective.ne hr)
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [quadraticSource, interpolatedSource, oddWeight, plus, minus, scale, map_mul,
      map_sub, map_pow, map_one, map_div₀] <;>
    field_simp [hden] <;> ring

private theorem interpolate_operator (h hD k rho a b : ℂ) (u v w : Row ℂᵣ) :
    rationalOperator h hD k (interpolatedSource rho a b u v w) =
      interpolatedSource rho a b (rationalOperator h hD k u)
        (rationalOperator h hD k v) (rationalOperator h hD k w) := by
  simp only [interpolatedSource, operator_plus, operator_constant_scale, operator_minus]

private theorem interpolate_plus_odd (rho a b : ℂ) (s₁ s₂ o d : Row ℂᵣ) :
    interpolatedSource rho a b s₁ s₂ (plus o d) =
      plus (interpolatedSource rho a b s₁ s₂ o) (scale (Cᵣ (oddWeight rho a b)) d) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [interpolatedSource, plus, scale, mul_add, add_assoc]

theorem exact_roots_of_obstruction (h hD k rho a b : ℂ)
    (p₁ p₂ shift first second odd remainder : Row ℂᵣ)
    (h₁ : rationalOperator h hD k p₁ = first)
    (h₂ : rationalOperator h hD k p₂ = second)
    (ho : odd = plus (rationalOperator h hD k shift) remainder)
    (exclude : ¬ ∃ p : Row ℂᵣ, rationalOperator h hD k p = remainder) :
    (∃ p : Row ℂᵣ, rationalOperator h hD k p = interpolatedSource rho a b first second odd) ↔
      b = a ∨ b = rho*a := by
  let base := interpolatedSource rho a b p₁ p₂ shift
  let s := oddWeight rho a b
  have factor : interpolatedSource rho a b first second odd =
      plus (rationalOperator h hD k base) (scale (Cᵣ s) remainder) := by
    rw [ho, interpolate_plus_odd]
    simp only [base, interpolate_operator, h₁, h₂, s]
  constructor
  · rintro ⟨p, hp⟩
    by_contra hz
    have hs : s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (fun e => hz (.inl e)))
      (sub_ne_zero.mpr (fun e => hz (.inr e)))
    have cancel : Cᵣ (s⁻¹) * Cᵣ s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs, map_one]
    refine exclude ⟨scale (Cᵣ (s⁻¹)) (minus p base), ?_⟩
    rw [operator_constant_scale, operator_minus, hp, factor]
    have residual : minus (plus (rationalOperator h hD k base) (scale (Cᵣ s) remainder))
        (rationalOperator h hD k base) = scale (Cᵣ s) remainder := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [plus, minus]
    rw [residual, scale_scale, cancel]
    simp [scale]
  · intro root
    have hz : s = 0 := by
      rcases root with root | root
      · simp [s, oddWeight, root]
      · simp [s, oddWeight, root]
    refine ⟨base, ?_⟩
    rw [factor, hz, map_zero]
    simp [plus, scale]

#print axioms exact_roots_of_obstruction

end
end SchwarzschildMixtures
