import AdmittedMixtureOperator
import MixturePolynomialCertificate

/-! The polynomial operations used to check the archived coefficients. -/
namespace SchwarzschildMixtures

open Polynomial SchwarzschildLaurent

noncomputable section

open NumeratorData

/-- The two radius-dependent denominator factors besides r and r - 2. -/
def parentPole (ell : ℂ) : ℂ[X] := X * C ((ell-1)*(ell+2)) + C 6
def daughterPole (ell : ℂ) : ℂ[X] := X * C ((2*ell-1)*(ell+1)) + C 3

def poles (ell : ℂ) : ℂ[X] := parentPole ell * daughterPole ell

def poleRate (ell : ℂ) : ℂ[X] :=
  11 * shiftedRadius * poles ell + X * poles ell +
    X * shiftedRadius * (5 * (parentPole ell).derivative * daughterPole ell +
      parentPole ell * (daughterPole ell).derivative)

/-- Apart from the radius-independent scalar, this is the denominator
of each of the two complete local fields. -/
def fieldDenominator (scalar ell : ℂ) : ℂ[X] :=
  C scalar * X^11 * shiftedRadius * (parentPole ell)^5 * daughterPole ell

theorem fieldDenominator_log (scalar ell : ℂ) :
    derivativeWeight (poles ell) * (fieldDenominator scalar ell).derivative =
      poleRate ell * fieldDenominator scalar ell := by
  simp only [fieldDenominator, poleRate, derivativeWeight, poles, derivative_mul,
    derivative_pow, derivative_C, derivative_X, derivative_sub, shiftedRadius,
    zero_mul, zero_add, mul_one, Nat.cast_ofNat, map_ofNat, Nat.reduceSubDiff, derivative_ofNat, sub_zero]
  ring

def rowValue (k ell : ℂ) (p : Row Expr) : Row ℂ[X] :=
  mapRow (Expr.value k ell) p

theorem x_value (k ell : ℂ) (j : ℕ) : Expr.value k ell (x j) = X^j := by
  simp [x, Expr.value_single]

private theorem c_value (k ell : ℂ) (a : ℤ) : Expr.value k ell (c a) = C (a : ℂ) :=
  Expr.value_constant k ell a

theorem parentPole_value (k ell : ℂ) :
    Expr.value k ell sparseParentPole = parentPole ell := by
  simp [sparseParentPole, l, x_value, c_value, parentPole, map_sub, map_add]

theorem daughterPole_value (k ell : ℂ) :
    Expr.value k ell sparseDaughterPole = daughterPole ell := by
  simp [sparseDaughterPole, u, l, x_value, c_value, daughterPole, map_sub, map_add]

theorem poles_value (k ell : ℂ) : Expr.value k ell sparsePoles = poles ell := by
  simp [sparsePoles, poles, parentPole_value, daughterPole_value]

private theorem rate_value (k ell : ℂ) (a b d : ℤ) :
    Expr.value k ell (rate a b d) = C (a : ℂ) * shiftedRadius * poles ell + X * poles ell +
      X * shiftedRadius * (C (b : ℂ) * (parentPole ell).derivative * daughterPole ell +
        C (d : ℂ) * parentPole ell * (daughterPole ell).derivative) := by
  simp [rate, xh, shiftedRadius, x_value, c_value, poles_value, parentPole_value, daughterPole_value]

private theorem second_rate_value (k ell : ℂ) :
    Expr.value k ell (rate 13 6 2) = secondRate (poles ell) (poleRate ell) := by
  rw [rate_value]
  push_cast
  simp only [map_ofNat, secondRate, poleRate, derivativeWeight, poles, derivative_mul]
  ring

private theorem first_rate_value (k ell : ℂ) :
    Expr.value k ell (rate 11 5 1) = poleRate ell := by
  rw [rate_value]
  push_cast
  simp only [map_ofNat, map_one, one_mul, poleRate]

private theorem jetA_value (k ell : ℂ) :
    Expr.value k ell jetAData = jetA (ell*(ell+1)) k := by
  simp [jetAData, jetA, c_value, x_value, w, h, l, map_add, pow_two]

private theorem jetB_value (k ell : ℂ) :
    Expr.value k ell jetBData = jetB := by
  simp [jetBData, jetB, xh, shiftedRadius, c_value, x_value, map_ofNat]

private theorem daughter_value (k ell : ℂ) :
    Expr.value k ell daughterData = daughterNumerator ((2*ell)*(2*ell+1)) k := by
  simp [daughterData, daughterNumerator, c_value, x_value, w, hD, u, l, xh, shiftedRadius,
    map_add, pow_two, map_ofNat]

theorem step_value (k ell : ℂ) (a b d : ℤ) (p : Row Expr) :
    rowValue k ell (stepData a b d p) =
      stepNumerator (ell*(ell+1)) k (poles ell) (Expr.value k ell (rate a b d)) (rowValue k ell p) := by
  simp only [rowValue, stepData, stepNumerator, scaleData, exprRowMap, mapRow, jetData, jetNumerator, jet,
    plus, minus, scale, Expr.value_add, Expr.value_sub, Expr.value_mul, Expr.value_derivative,
    poles_value, jetA_value, jetB_value, c_value, Int.cast_ofNat, map_ofNat, derivativeWeight,
    x_value, pow_one, xh, shiftedRadius, one_mul, mul_one, add_sub_assoc]

theorem sourceData_correct (k ell : ℂ) (p : Row Expr) :
    rowValue k ell (sourceData p) =
      operatorNumerator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k (poles ell) (poleRate ell) (rowValue k ell p) := by
  calc
    _ = minus (rowValue k ell (stepData 13 6 2 (stepData 11 5 1 p)))
          (scale ((poles ell)^2 * daughterNumerator ((2*ell)*(2*ell+1)) k) (rowValue k ell p)) := by
      simp only [sourceData, rowValue, subData, minus, scale, mapRow, scaleData, exprRowMap,
        Expr.value_sub, Expr.value_mul, poles_value, daughter_value, pow_two, mul_assoc]
    _ = _ := by rw [step_value, step_value, first_rate_value, second_rate_value, operatorNumerator]

/-- Use the actual common denominator of the stored field coefficients.
The right-hand side has the two extra factors used in the differentiated row. -/
theorem source_of_checked_numerators (k ell scalar : ℂ) (field source : Row Expr)
    (hq : fieldDenominator scalar ell ≠ 0) (hb : poles ell ≠ 0)
    (checked : rowValue k ell (sourceData field) = rowValue k ell source) :
    rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k
      (fractionRow (rowValue k ell field) (fieldDenominator scalar ell)) =
    fractionRow (rowValue k ell source)
      (denominatorStep (poles ell) * (denominatorStep (poles ell) * fieldDenominator scalar ell)) := by
  rw [fraction_operator _ _ _ _ _ _ _ hq hb (fieldDenominator_log scalar ell),
    ← sourceData_correct, checked]

end
end SchwarzschildMixtures
