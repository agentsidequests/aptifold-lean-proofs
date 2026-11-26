import RationalLaurent

/-!
Normalized coefficients of the Laurent operator at finite points.
The source equality is read after clearing the local denominator and
extracting the candidate's leading radial power.
-/

namespace SchwarzschildLaurent

open Polynomial

noncomputable section

def rowEval (a : ℂ) (p : Row ℂ[X]) : Row ℂ :=
  (p.1.eval a, p.2.1.eval a, p.2.2.eval a)

def rowDerivative (p : Row ℂ[X]) : Row ℂ[X] :=
  (p.1.derivative, p.2.1.derivative, p.2.2.derivative)

theorem rowEval_scale (a : ℂ) (s : ℂ[X]) (p : Row ℂ[X]) :
    rowEval a (scale s p) = scale (s.eval a) (rowEval a p) := by
  simp [rowEval, scale, eval_mul]

def rowEuler (a : ℂ) (m : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  (eulerNumerator a m p.1 q, eulerNumerator a m p.2.1 q, eulerNumerator a m p.2.2 q)

/-- Numerator over q⁴ after factoring t^(-m) out of the Euler operator.
The three coefficients multiply E²-E, E and the undifferentiated row. -/
def eulerResidual (a : ℂ) (m : ℕ) (q : ℂ[X]) (p : Row ℂ[X])
    (α : ℂ[X]) (β γ : Row ℂ[X] → Row ℂ[X]) : Row ℂ[X] :=
  let first := rowEuler a m q p
  let second := rowEuler a m (q^2) first
  plus (scale α (minus second (scale (q^2) first)))
    (plus (β (scale (q^2) first)) (γ (scale (q^3) p)))

def shiftedRadius : ℂ[X] := X - C 2

/-- The r²-scaled coefficients of the quadratic jet matrix in (J²,JZ,Z²). -/
def jetA (h k : ℂ) : ℂ[X] :=
  X^4 * C (k^2) + X^2 * C h - X * C (2*h+6) + C 12

def jetB : ℂ[X] := 2 * shiftedRadius

def jetNumerator (h k : ℂ) (p : Row ℂ[X]) : Row ℂ[X] :=
  jet (jetA h k) jetB 1 p

def jetNumeratorDerivative (h k : ℂ) (p : Row ℂ[X]) : Row ℂ[X] :=
  jet (jetA h k).derivative jetB.derivative 0 p

/-- The coefficient of the second derivative in r⁴ times the row equation. -/
def secondCoefficient : ℂ[X] := X^2 * shiftedRadius^2

/-- The coefficient of the first derivative in r⁴ times the row equation. -/
def firstCoefficient (h k : ℂ) (p : Row ℂ[X]) : Row ℂ[X] :=
  scale (2 * X * shiftedRadius) (plus p (jetNumerator h k p))

/-- The undifferentiated coefficient in r⁴ times the row equation. -/
def zeroCoefficient (h hD k : ℂ) (p : Row ℂ[X]) : Row ℂ[X] :=
  plus (scale shiftedRadius
      (minus (scale X (jetNumeratorDerivative h k p)) (scale 2 (jetNumerator h k p))))
    (minus (jetNumerator h k (jetNumerator h k p))
      (scale (C (4*k^2)*X^4 + shiftedRadius*(C hD*X-6)) p))

/-- Ordinary point. Multiplication by t² clears the two Euler denominators. -/
def ordinaryResidual (h hD k a : ℂ) (m : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  eulerResidual a m q p secondCoefficient
    (fun v => scale (localCoordinate a) (firstCoefficient h k v))
    (fun v => scale (localCoordinate a ^ 2) (zeroCoefficient h hD k v))

/-- Origin. The coefficients already contain the necessary factors r² and r. -/
def originResidual (h hD k : ℂ) (m : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  eulerResidual 0 m q p (shiftedRadius^2)
    (fun v => scale (2*shiftedRadius) (plus v (jetNumerator h k v)))
    (zeroCoefficient h hD k)

/-- Horizon. The coefficients already contain the factors (r-2)² and (r-2). -/
def horizonResidual (h hD k : ℂ) (m : ℕ) (q : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  eulerResidual 2 m q p (X^2)
    (fun v => scale (2*X) (plus v (jetNumerator h k v)))
    (zeroCoefficient h hD k)

private theorem originIndicial_jet (m : ℂ) (u : Row ℂ) :
    originIndicial m u =
      minus (plus (jet 12 (-4) 1 (plus (jet 12 (-4) 1 u) (scale (2*m) u)))
                  (scale (2*m+4) (plus (jet 12 (-4) 1 u) (scale (2*m) u))))
            (scale 12 u) := rfl

private def unscaledAtHorizon (u : Row ℂ) : Row ℂ :=
  (u.1, 4*u.2.1, 16*u.2.2)

private theorem horizonIndicial_jet (k δ : ℂ) (u : Row ℂ) :
    horizonIndicial k δ u =
      minus (plus (jet (k^2) 0 1 (plus (jet (k^2) 0 1 u) (scale δ u)))
                  (scale δ (plus (jet (k^2) 0 1 u) (scale δ u))))
            (scale (4*k^2) u) := rfl

theorem ordinary_residual_coefficient (h hD k a : ℂ) (m : ℕ)
    (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval a (ordinaryResidual h hD k a m q p) =
      scale (q.eval a ^ 3) (ordinaryIndicial (a*(a-2)) m (rowEval a p)) := by
  apply Prod.ext
  · simp [rowEval, ordinaryResidual, eulerResidual, secondCoefficient, ordinaryIndicial, plus,
      minus, scale, rowEuler, shiftedRadius, localCoordinate, eulerNumerator_eval]
    ring
  · apply Prod.ext <;>
    simp [rowEval, ordinaryResidual, eulerResidual, secondCoefficient, ordinaryIndicial, plus,
      minus, scale, rowEuler, shiftedRadius, localCoordinate, eulerNumerator_eval] <;> ring

theorem origin_residual_coefficient (h hD k : ℂ) (m : ℕ)
    (q : ℂ[X]) (p : Row ℂ[X]) :
    rowEval 0 (originResidual h hD k m q p) =
      scale (q.eval 0 ^ 3) (originIndicial (m : ℂ) (rowEval 0 p)) := by
  rw [originIndicial_jet]
  apply Prod.ext
  · norm_num [rowEval, originResidual, eulerResidual, zeroCoefficient, jetNumerator,
      jetNumeratorDerivative, jetA, jetB, shiftedRadius, jet, plus, minus, scale, rowEuler,
      eulerNumerator_twice_eval, eulerNumerator_eval]
    ring
  · apply Prod.ext <;> norm_num [rowEval, originResidual, eulerResidual, zeroCoefficient, jetNumerator,
      jetNumeratorDerivative, jetA, jetB, shiftedRadius, jet, plus, minus, scale, rowEuler,
      eulerNumerator_twice_eval, eulerNumerator_eval] <;> ring

theorem horizon_residual_coefficient (h hD k : ℂ) (m : ℕ)
    (q : ℂ[X]) (p : Row ℂ[X]) :
    unscaledAtHorizon (rowEval 2 (horizonResidual h hD k m q p)) =
      scale (16 * q.eval 2 ^ 3)
        (horizonIndicial k ((-(m : ℝ)/2 : ℝ) : ℂ) (unscaledAtHorizon (rowEval 2 p))) := by
  rw [horizonIndicial_jet]
  apply Prod.ext
  · norm_num [rowEval, horizonResidual, eulerResidual, zeroCoefficient, jetNumerator,
      unscaledAtHorizon, jetNumeratorDerivative, jetA, jetB, shiftedRadius, jet, plus, minus,
      scale, rowEuler, eulerNumerator_twice_eval, eulerNumerator_eval]
    ring
  · apply Prod.ext <;> norm_num [rowEval, horizonResidual, eulerResidual, zeroCoefficient, jetNumerator,
      unscaledAtHorizon, jetNumeratorDerivative, jetA, jetB, shiftedRadius, jet, plus, minus,
      scale, rowEuler, eulerNumerator_twice_eval, eulerNumerator_eval] <;> ring

theorem ordinary_bound_from_residual (h hD k a : ℂ) (m : ℕ) (hm : 0 < m)
    (ha : a ≠ 0) (ha₂ : a ≠ 2) (q : ℂ[X]) (p : Row ℂ[X]) (hq : q.eval a ≠ 0)
    (hzero : rowEval a (ordinaryResidual h hD k a m q p) = 0) :
    rowEval a p = 0 := by
  by_contra hn
  rw [ordinary_residual_coefficient] at hzero
  exact ordinary_pole_forces_leading_term m hm (a*(a-2)) (mul_ne_zero ha (sub_ne_zero.mpr ha₂))
    hn (scale_eq_zero (pow_ne_zero _ hq) hzero)

theorem origin_bound_from_residual (h hD k : ℂ) (m : ℕ) (q : ℂ[X]) (p : Row ℂ[X])
    (hq : q.eval 0 ≠ 0) (hp : rowEval 0 p ≠ 0)
    (hzero : rowEval 0 (originResidual h hD k m q p) = 0) (hm : 0 < m) : m ≤ 7 := by
  rw [origin_residual_coefficient] at hzero
  rcases origin_pole_resonances m hm _ hp (scale_eq_zero (pow_ne_zero _ hq) hzero) with rfl | rfl <;> decide

theorem horizon_bound_from_residual (h hD k : ℂ) (hk : k ≠ 0) (hi : k.re = 0)
    (m : ℕ) (hm : 0 < m) (q : ℂ[X]) (p : Row ℂ[X]) (hq : q.eval 2 ≠ 0)
    (hzero : rowEval 2 (horizonResidual h hD k m q p) = 0) : rowEval 2 p = 0 := by
  have hzero' := congrArg unscaledAtHorizon hzero
  rw [horizon_residual_coefficient, show unscaledAtHorizon 0 = 0 by simp [unscaledAtHorizon]] at hzero'
  have h := horizon_no_pole m hm k hk hi _ (scale_eq_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hq)) hzero')
  apply Prod.ext
  · have hf := congrArg (fun u : Row ℂ => u.1) h
    exact hf
  · apply Prod.ext
    · exact (mul_eq_zero.mp (congrArg (fun u => u.2.1) h)).resolve_left (by norm_num)
    · exact (mul_eq_zero.mp (congrArg (fun u => u.2.2) h)).resolve_left (by norm_num)

#print axioms ordinary_bound_from_residual
#print axioms origin_bound_from_residual
#print axioms horizon_bound_from_residual

end

end SchwarzschildLaurent
