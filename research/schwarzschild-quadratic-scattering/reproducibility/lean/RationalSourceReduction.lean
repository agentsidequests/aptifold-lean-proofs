import NormalizedRowOperator

/-! The pole and degree bounds apply to a rational equation with the archived source orders. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)

theorem scale_injective {A : Type*} [CommRing A] [IsDomain A] {a : A} (ha : a ≠ 0) :
    Function.Injective (scale a : Row A → Row A) := by
  intro u v hv
  apply Prod.ext
  · exact mul_left_cancel₀ ha (congrArg Prod.fst hv)
  · exact Prod.ext
      (mul_left_cancel₀ ha (congrArg (fun p => p.2.1) hv))
      (mul_left_cancel₀ ha (congrArg (fun p => p.2.2) hv))

theorem scale_zero_row {A : Type*} [Ring A] (a : A) : scale a (0 : Row A) = 0 := by
  simp [scale]

theorem zero_scale_row {A : Type*} [Ring A] (u : Row A) : scale 0 u = 0 := by
  simp [scale]

private theorem poly_ne_zero_of_eval {a : ℂ} {q : ℂ[X]} (hq : q.eval a ≠ 0) : q ≠ 0 := by
  intro h
  exact hq (by simp [h])

private theorem local_fraction_den_ne_zero (a : ℂ) (m : ℕ) {q : ℂ[X]} (hq : q ≠ 0) :
    localCoordinate a^m*q ≠ 0 := mul_ne_zero (pow_ne_zero m (localCoordinate_ne_zero a)) hq

/-- A denominator of the form r^m q on one side and r^b on the other forces the
    first numerator to contain r^(m-b) if b ≤ m. -/
private theorem strip_radius_denominator (p s : Row ℂ[X]) (m b : ℕ) (q : ℂ[X]) (hq : q ≠ 0)
    (hb : b ≤ m) (e : fractionRow p (X^m*q) = fractionRow s (X^b)) :
    p = scale (X^(m-b)*q) s := by
  have eq := fractionRow_cross p s _ _
    (mul_ne_zero (pow_ne_zero m Polynomial.X_ne_zero) hq) (pow_ne_zero b Polynomial.X_ne_zero) e
  apply scale_injective (pow_ne_zero b Polynomial.X_ne_zero)
  rw [scale_scale, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hb]
  exact eq

/-- The algebraic source orders needed by the finite and infinity arguments. -/
structure SourceOrders (s : Row ℂᵣ) : Prop where
  finite : ∃ p : Row ℂ[X], s = fractionRow p (X^6)
  infinity : ∃ p : Row ℂ[X], reciprocalRow (unscaledRow s) = fractionRow p (X^3)

theorem finiteEquations_of_rational (h hD k : ℂ) (u s : Row ℂᵣ) (eq : rationalOperator h hD k u = s)
    (source : ∃ p : Row ℂ[X], s = fractionRow p (X^6)) : FiniteSourceEquations h hD k u := by
  obtain ⟨src, hsrc⟩ := source
  have hx (n : ℕ) : (X : ℂ[X])^n ≠ 0 := pow_ne_zero n Polynomial.X_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro a q p ha _ hm hq hu
    have hq' := poly_ne_zero_of_eval hq
    have e := ordinaryResidual_correct h hD k a (poleOrder u a) q hq' p
    rw [← hu, eq, hsrc, ← RatFunc.algebraMap_X, ← map_pow, ← map_pow, ← map_mul, ← fractionRow_scale] at e
    have e' := fractionRow_cross _ _ _ _
      (local_fraction_den_ne_zero a (poleOrder u a) (pow_ne_zero 4 hq')) (hx 6) e
    have eval := congrArg (rowEval a) e'
    simp only [rowEval_scale, eval_mul, eval_pow, eval_X, localCoordinate, eval_sub, eval_C,
      sub_self, zero_pow (by omega : poleOrder u a ≠ 0), zero_mul, zero_scale_row] at eval
    exact scale_injective (pow_ne_zero 6 ha) (eval.trans (scale_zero_row (a^6)).symm)
  · intro q p hm hq hu
    have hq' := poly_ne_zero_of_eval hq
    have e := horizonResidual_correct h hD k (poleOrder u 2) q hq' p
    rw [← hu, eq, hsrc, ← RatFunc.algebraMap_X, ← map_pow, ← fractionRow_scale] at e
    have e' := fractionRow_cross _ _ _ _
      (local_fraction_den_ne_zero 2 (poleOrder u 2) (pow_ne_zero 4 hq')) (hx 6) e
    have eval := congrArg (rowEval 2) e'
    simp only [rowEval_scale, eval_mul, eval_pow, eval_X, localCoordinate, eval_sub, eval_C,
      sub_self, zero_pow (by omega : poleOrder u 2 ≠ 0), zero_mul, zero_scale_row] at eval
    exact scale_injective (pow_ne_zero 6 (by norm_num : (2 : ℂ) ≠ 0))
      (eval.trans (scale_zero_row ((2 : ℂ)^6)).symm)
  · intro q p hm hq hu
    have hq' := poly_ne_zero_of_eval hq
    rw [localCoordinate_zero] at hu
    have e := originResidual_correct h hD k (poleOrder u 0) q hq' p
    rw [← hu, eq, hsrc, ← RatFunc.algebraMap_X, ← map_pow, ← fractionRow_scale,
      show (X : ℂ[X])^6 = X^4*X^2 by ring, fractionRow_cancel _ (hx 4)] at e
    have e' := strip_radius_denominator _ _ _ 2 (q^4) (pow_ne_zero 4 hq') (by omega) e
    rw [e', rowEval_scale]
    simp only [eval_mul, eval_pow, eval_X, zero_pow (by omega : poleOrder u 0 - 2 ≠ 0),
      zero_mul, zero_scale_row]

theorem infinityEquation_of_rational (h hD k : ℂ) (u s : Row ℂᵣ) (eq : rationalOperator h hD k u = s)
    (source : ∃ p : Row ℂ[X], reciprocalRow (unscaledRow s) = fractionRow p (X^3)) :
    InfinitySourceEquation h hD k u := by
  obtain ⟨src, hsrc⟩ := source
  intro q p hq hu hm
  let d := growth (unscaledRow u)
  change 4 < d at hm
  change reciprocalRow (unscaledRow u) = fractionRow p (X^d*q) at hu
  have hq' := poly_ne_zero_of_eval hq
  have e := infinityResidual_correct h hD k d q hq' p
  rw [← hu, ← reciprocal_operator_correct, eq, hsrc] at e
  have strip := strip_radius_denominator _ _ d 3 (q^4) (pow_ne_zero 4 hq') (by omega) e
  refine ⟨scale (X^(d-5)*q^4) src, ?_⟩
  change infinityResidual h hD k d q p = _
  rw [strip, scale_scale, ← mul_assoc, ← pow_add, show 2+(d-5)=d-3 by omega]

/-- For the rescaled source orders, every solution of the actual rational differential
    equation lies in the 12 + 10 + 8 columns of the consistency matrix. -/
theorem matrix_span_from_rational_row (h hD k : ℂ) (hk : k ≠ 0) (hi : k.re = 0)
    (u s : Row ℂᵣ) (eq : rationalOperator h hD k u = s) (orders : SourceOrders s) :
    ∃ coeff : Row (ℕ → ℂ),
      u = (laurentSpan 12 coeff.1, laurentSpan 10 coeff.2.1, laurentSpan 8 coeff.2.2) := by
  exact matrix_span_from_normalized_equations h hD k hk hi u
    (finiteEquations_of_rational h hD k u s eq orders.finite)
    (infinityEquation_of_rational h hD k u s eq orders.infinity)

#print axioms finiteEquations_of_rational
#print axioms infinityEquation_of_rational
#print axioms matrix_span_from_rational_row

end

end SchwarzschildLaurent
