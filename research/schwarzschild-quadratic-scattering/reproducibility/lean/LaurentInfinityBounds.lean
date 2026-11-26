import LaurentOperatorBounds

/-!
The constant and linear terms in t = 1/r of the normalized operator.
The basis here is (J², J DJ, (DJ)²).
-/

namespace SchwarzschildLaurent

open Polynomial

noncomputable section

def infinityPotential (h : ℂ) : ℂ[X] :=
  (1-2*X)*(C h*X^2-6*X^3)

def infinityVelocity : ℂ[X] := -(X*(1-2*X))

def infinityJetA (h k : ℂ) : ℂ[X] := C (k^2) + infinityPotential h

def infinityDaughter (hD k : ℂ) : ℂ[X] := C (4*k^2) + infinityPotential hD

def rowEulerZero (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  (eulerNumerator 0 d p.1 q, eulerNumerator 0 d p.2.1 q, eulerNumerator 0 d p.2.2 q)

/-- Numerator over q² of the derivative and jet terms, with t^(-d) extracted. -/
def infinityDerivativeNumerator (h k : ℂ) (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  plus (scale infinityVelocity (rowEulerZero d q p))
    (jet (infinityJetA h k) 0 1 (scale q p))

/-- Numerator over q⁴ of the daughter equation with t^(-d) extracted. -/
def infinityResidual (h hD k : ℂ) (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  minus (infinityDerivativeNumerator h k d (q^2) (infinityDerivativeNumerator h k d q p))
    (scale (infinityDaughter hD k*q^3) p)

private theorem rowEval_add (a : ℂ) (p q : Row ℂ[X]) :
    rowEval a (plus p q) = plus (rowEval a p) (rowEval a q) := by simp [rowEval, plus]

private theorem rowEval_sub (a : ℂ) (p q : Row ℂ[X]) :
    rowEval a (minus p q) = minus (rowEval a p) (rowEval a q) := by simp [rowEval, minus]

private theorem rowEval_jet (a : ℂ) (b c d : ℂ[X]) (p : Row ℂ[X]) :
    rowEval a (jet b c d p) = jet (b.eval a) (c.eval a) (d.eval a) (rowEval a p) := by
  simp [rowEval, jet]

private theorem derivative_add_row (p q : Row ℂ[X]) :
    rowDerivative (plus p q) = plus (rowDerivative p) (rowDerivative q) := by
  simp [rowDerivative, plus, Polynomial.derivative_add]

private theorem derivative_sub_row (p q : Row ℂ[X]) :
    rowDerivative (minus p q) = minus (rowDerivative p) (rowDerivative q) := by
  simp [rowDerivative, minus, Polynomial.derivative_sub]

private theorem derivative_scale_row (b : ℂ[X]) (p : Row ℂ[X]) :
    rowDerivative (scale b p) = plus (scale b.derivative p) (scale b (rowDerivative p)) := by
  simp [rowDerivative, plus, scale, Polynomial.derivative_mul]

private theorem derivative_jet_row (a b c : ℂ[X]) (p : Row ℂ[X]) :
    rowDerivative (jet a b c p) =
      plus (jet a.derivative b.derivative c.derivative p) (jet a b c (rowDerivative p)) := by
  apply Prod.ext
  · simp [rowDerivative, plus, jet, Polynomial.derivative_mul]
  · apply Prod.ext <;>
    simp [rowDerivative, plus, jet, Polynomial.derivative_add, Polynomial.derivative_mul] <;> ring

private theorem infinityPotential_eval (h : ℂ) : (infinityPotential h).eval 0 = 0 := by
  simp [infinityPotential]

private theorem infinityPotential_derivative_eval (h : ℂ) :
    (infinityPotential h).derivative.eval 0 = 0 := by
  norm_num [infinityPotential, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow]

private theorem infinityVelocity_eval : infinityVelocity.eval 0 = 0 := by simp [infinityVelocity]

private theorem infinityVelocity_derivative_eval : infinityVelocity.derivative.eval 0 = -1 := by
  norm_num [infinityVelocity, Polynomial.derivative_neg, Polynomial.derivative_sub, Polynomial.derivative_mul]

private theorem infinityJetA_eval (h k : ℂ) : (infinityJetA h k).eval 0 = k^2 := by
  simp [infinityJetA, infinityPotential_eval]

private theorem infinityJetA_derivative_eval (h k : ℂ) :
    (infinityJetA h k).derivative.eval 0 = 0 := by
  simp only [infinityJetA, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
    infinityPotential_derivative_eval]

private theorem infinityDaughter_eval (hD k : ℂ) : (infinityDaughter hD k).eval 0 = 4*k^2 := by
  simp [infinityDaughter, infinityPotential_eval]

private theorem infinityDaughter_derivative_eval (hD k : ℂ) :
    (infinityDaughter hD k).derivative.eval 0 = 0 := by
  simp only [infinityDaughter, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
    infinityPotential_derivative_eval]

private theorem rowEulerZero_eval (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval 0 (rowEulerZero d q p) = scale (-(d : ℂ) * q.eval 0) (rowEval 0 p) := by
  simp [rowEval, rowEulerZero, scale, eulerNumerator_eval, mul_right_comm]

private theorem infinityDerivative_value (h k : ℂ) (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval 0 (infinityDerivativeNumerator h k d q p) =
      scale (q.eval 0) (jet (k^2) 0 1 (rowEval 0 p)) := by
  simp only [infinityDerivativeNumerator, rowEval_add, rowEval_scale, rowEval_jet,
    infinityVelocity_eval, infinityJetA_eval, Polynomial.eval_zero, Polynomial.eval_one]
  apply Prod.ext
  · simp [scale, plus, jet]; ring
  · apply Prod.ext
    · simp [scale, plus, jet]
      ring
    · simp [scale, plus, jet]

private theorem infinityDerivative_slope (h k : ℂ) (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval 0 (rowDerivative (infinityDerivativeNumerator h k d q p)) =
      plus (scale (q.eval 0) (plus (scale (d : ℂ) (rowEval 0 p))
        (jet (k^2) 0 1 (rowEval 0 (rowDerivative p)))))
        (scale (q.derivative.eval 0) (jet (k^2) 0 1 (rowEval 0 p))) := by
  simp only [infinityDerivativeNumerator, derivative_add_row, derivative_scale_row, derivative_jet_row,
    rowEval_add, rowEval_scale, rowEval_jet, infinityVelocity_derivative_eval, infinityVelocity_eval,
    infinityJetA_derivative_eval, infinityJetA_eval, derivative_zero, derivative_one, eval_zero, eval_one,
    rowEulerZero_eval]
  apply Prod.ext
  · simp [scale, plus, jet]; ring
  · apply Prod.ext <;> simp [scale, plus, jet] <;> ring

private theorem infinityLeading_jet (k : ℂ) (u : Row ℂ) :
    infinityLeading k u = minus (jet (k^2) 0 1 (jet (k^2) 0 1 u)) (scale (4*k^2) u) := rfl

private theorem infinityNext_jet (k d : ℂ) (u v : Row ℂ) :
    infinityNext k d u v = plus (infinityLeading k v) (scale (2*d) (jet (k^2) 0 1 u)) := rfl

theorem infinity_residual_value (h hD k : ℂ) (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval 0 (infinityResidual h hD k d q p) =
      scale (q.eval 0 ^ 3) (infinityLeading k (rowEval 0 p)) := by
  simp only [infinityResidual, rowEval_sub, infinityDerivative_value, eval_pow, rowEval_scale,
    eval_mul, infinityDaughter_eval, infinityLeading_jet]
  apply Prod.ext
  · simp [scale, minus, jet]; ring
  · apply Prod.ext <;> simp [scale, minus, jet] <;> ring

theorem infinity_residual_slope (h hD k : ℂ) (d : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval 0 (rowDerivative (infinityResidual h hD k d q p)) =
      plus (scale (q.eval 0 ^ 3) (infinityNext k (d : ℂ) (rowEval 0 p)
        (rowEval 0 (rowDerivative p))))
        (scale (3 * q.eval 0 ^ 2 * q.derivative.eval 0) (infinityLeading k (rowEval 0 p))) := by
  simp only [infinityResidual, derivative_sub_row, derivative_scale_row, rowEval_sub, rowEval_add,
    rowEval_scale, infinityDerivative_slope, infinityDerivative_value,
    Polynomial.derivative_mul, Polynomial.derivative_pow, eval_add, eval_mul, eval_pow, eval_C,
    infinityDaughter_eval, infinityDaughter_derivative_eval, infinityNext_jet, infinityLeading_jet]
  apply Prod.ext
  · norm_num [scale, minus, plus, jet]; ring
  · apply Prod.ext <;> norm_num [scale, minus, plus, jet] <;> ring

/-- A source with vanishing constant and linear terms cannot drive a degree
above four. For a source growing at most as r³ these terms vanish after
extracting t^(-d) whenever d > 4. -/
theorem infinity_degree_bound (h hD k : ℂ) (hk : k ≠ 0) (d : ℕ)
    (q : ℂ[X]) (hq : q.eval 0 ≠ 0) (p : Row ℂ[X]) (hp : rowEval 0 p ≠ 0)
    (source : 4 < d → ∃ v : Row ℂ[X], infinityResidual h hD k d q p = scale (X^2) v) :
    d ≤ 4 := by
  by_contra hn
  have hd₄ : 4 < d := by omega
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨v, hv⟩ := source hd₄
  have hzero : rowEval 0 (infinityResidual h hD k d q p) = 0 := by
    rw [hv, rowEval_scale]
    simp [scale]
  have hone : rowEval 0 (rowDerivative (infinityResidual h hD k d q p)) = 0 := by
    rw [hv, derivative_scale_row, rowEval_add, rowEval_scale, rowEval_scale]
    norm_num [Polynomial.derivative_pow, scale, plus]
  rw [infinity_residual_value] at hzero
  have hfirst := scale_eq_zero (pow_ne_zero 3 hq) hzero
  rw [infinity_residual_slope, hfirst] at hone
  have hsecond : infinityNext k (d : ℂ) (rowEval 0 p) (rowEval 0 (rowDerivative p)) = 0 := by
    apply scale_eq_zero (pow_ne_zero 3 hq)
    simpa [plus, scale] using hone
  exact hp (infinity_two_equations k (d : ℂ) hk hd _ _ hfirst hsecond)

#print axioms infinity_degree_bound

end

end SchwarzschildLaurent
