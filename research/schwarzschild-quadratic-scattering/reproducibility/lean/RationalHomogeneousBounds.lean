import RationalSourceReduction

/-! A homogeneous rational quadratic row has zero growth in the
unscaled parent basis. Only 8 + 6 + 4 Laurent coefficients can remain. -/
namespace SchwarzschildLaurent

open Polynomial
open scoped BigOperators

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

private theorem reciprocal_unscaled_zero :
    reciprocalRow (unscaledRow (0 : Row ℂᵣ)) = 0 := by
  simp [reciprocalRow_eq_hom,unscaledRow,mapRow]

theorem zero_source_orders : SourceOrders (0 : Row ℂᵣ) := by
  refine ⟨⟨0,?_⟩,⟨0,?_⟩⟩
  · simp [fractionRow]; rfl
  · rw [reciprocal_unscaled_zero]
    simp [fractionRow]; rfl

theorem homogeneous_growth_zero (h hD k : ℂ) (hk : k ≠ 0) (u : Row ℂᵣ)
    (eq : rationalOperator h hD k u = 0) : growth (unscaledRow u) = 0 := by
  let d := growth (unscaledRow u)
  by_contra nonzero
  have dpos : 0 < d := Nat.pos_of_ne_zero nonzero
  have dn : (d:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr dpos.ne'
  obtain ⟨q,p,hq,representation,lead⟩ := normalize_at_infinity (unscaledRow u)
  have q0 : q ≠ 0 := fun hz => hq (by simp [hz])
  have residual := infinityResidual_correct h hD k d q q0 p
  rw [← representation,← reciprocal_operator_correct,eq,reciprocal_unscaled_zero] at residual
  have asFraction : fractionRow (infinityResidual h hD k d q p) (X^d*q^4) =
      fractionRow (0 : Row ℂ[X]) 1 := by simpa [fractionRow] using residual
  have raw := fractionRow_cross _ _ _ _ (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ q0))
    one_ne_zero asFraction
  have vanish : infinityResidual h hD k d q p = 0 := by
    change infinityResidual h hD k d q p = (0,0,0)
    simpa [scale] using raw
  have value : rowEval 0 (infinityResidual h hD k d q p) = 0 := by simp [vanish,rowEval]
  have slope : rowEval 0 (rowDerivative (infinityResidual h hD k d q p)) = 0 := by
    simp [vanish,rowEval,rowDerivative]
  rw [infinity_residual_value] at value
  have first := scale_eq_zero (pow_ne_zero 3 hq) value
  rw [infinity_residual_slope,first] at slope
  have second : infinityNext k (d:ℂ) (rowEval 0 p) (rowEval 0 (rowDerivative p)) = 0 := by
    apply scale_eq_zero (pow_ne_zero 3 hq)
    simpa [plus,scale] using slope
  exact (lead dpos) (infinity_two_equations k (d:ℂ) hk dn _ _ first second)

private theorem shrink_laurent_span (u : ℂᵣ) (full shift : ℕ) (shift_bound : shift ≤ 7)
    (coeff : ℕ → ℂ) (span : u = laurentSpan full coeff)
    (degree : (u*(RatFunc.X : ℂᵣ)^shift).num.natDegree ≤ (u*(RatFunc.X : ℂᵣ)^shift).denom.natDegree) :
    ∃ c : ℕ → ℂ, u = laurentSpan (8-shift) c := by
  by_cases zero : u = 0
  · exact ⟨0,by simp only [zero,laurentSpan,Pi.zero_apply,map_zero,zero_mul,Finset.sum_const_zero]⟩
  let p : ℂ[X] := ∑ i ∈ Finset.range full, C (coeff i)*X^i
  have ep : u = ι p/(RatFunc.X : ℂᵣ)^7 := by
    rw [span]
    simp only [p,laurentSpan,map_sum,map_mul,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [zpow_sub₀ RatFunc.X_ne_zero,zpow_natCast,
      show ((7 : ℤ)) = ((7 : ℕ) : ℤ) from rfl,zpow_natCast,mul_div_assoc]
  have p0 : p ≠ 0 := fun hp => zero (by simp [ep,hp])
  let v := u*(RatFunc.X : ℂᵣ)^shift
  have v0 : v ≠ 0 := mul_ne_zero zero (pow_ne_zero _ RatFunc.X_ne_zero)
  have vform : v = ι (p*X^shift)/ι ((X:ℂ[X])^7) := by
    dsimp only [v]
    rw [ep]
    simp only [map_mul,map_pow,RatFunc.algebraMap_X]
    ring
  have mulEq := (RatFunc.num_mul_eq_mul_denom_iff (pow_ne_zero 7 Polynomial.X_ne_zero)).mpr vform
  have degEq := congrArg natDegree mulEq
  rw [natDegree_mul (RatFunc.num_ne_zero v0) (pow_ne_zero _ Polynomial.X_ne_zero),
    natDegree_mul (mul_ne_zero p0 (pow_ne_zero _ Polynomial.X_ne_zero)) v.denom_ne_zero,
    natDegree_mul p0 (pow_ne_zero _ Polynomial.X_ne_zero),natDegree_X_pow,natDegree_X_pow] at degEq
  have degP : p.natDegree < 8-shift := by change v.num.natDegree ≤ v.denom.natDegree at degree; omega
  refine ⟨p.coeff,?_⟩
  have exp := p.as_sum_range_C_mul_X_pow' (n := 8-shift) degP
  rw [ep]
  conv_lhs => rw [exp]
  simp only [laurentSpan,map_sum,map_mul,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ RatFunc.X_ne_zero,zpow_natCast,
    show ((7 : ℤ)) = ((7 : ℕ) : ℤ) from rfl,zpow_natCast,mul_div_assoc]

theorem short_span_for_homogeneous_row (h hD k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (u : Row ℂᵣ) (eq : rationalOperator h hD k u = 0) :
    ∃ coeff : Row (ℕ → ℂ), u = (laurentSpan 8 coeff.1,laurentSpan 6 coeff.2.1,laurentSpan 4 coeff.2.2) := by
  obtain ⟨big,span⟩ := matrix_span_from_rational_row h hD k hk ki u 0 eq zero_source_orders
  have d := homogeneous_growth_zero h hD k hk u eq
  simp only [growth,componentGrowth,unscaledRow] at d
  have h₀ : u.1.num.natDegree ≤ u.1.denom.natDegree := by omega
  have h₁ : (u.2.1*(RatFunc.X : ℂᵣ)^2).num.natDegree ≤ (u.2.1*(RatFunc.X : ℂᵣ)^2).denom.natDegree := by omega
  have h₂ : (u.2.2*(RatFunc.X : ℂᵣ)^4).num.natDegree ≤ (u.2.2*(RatFunc.X : ℂᵣ)^4).denom.natDegree := by omega
  obtain ⟨a,ha⟩ := shrink_laurent_span u.1 12 0 (by decide) big.1 (congrArg Prod.fst span) (by simpa using h₀)
  obtain ⟨b,hb⟩ := shrink_laurent_span u.2.1 10 2 (by decide) big.2.1
    (congrArg (fun x => x.2.1) span) h₁
  obtain ⟨c,hc⟩ := shrink_laurent_span u.2.2 8 4 (by decide) big.2.2
    (congrArg (fun x => x.2.2) span) h₂
  exact ⟨(a,b,c),Prod.ext ha (Prod.ext hb hc)⟩

#print axioms homogeneous_growth_zero
#print axioms short_span_for_homogeneous_row

end
end SchwarzschildLaurent
