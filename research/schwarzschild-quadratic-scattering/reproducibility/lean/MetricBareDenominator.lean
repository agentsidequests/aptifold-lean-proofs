import AdmittedMixtureField
import ExactRationalSoundness
import MetricBareFinishData

/-! Interpret the exact coefficient certificate's denominator in the rational operator. -/
namespace SchwarzschildMixtures

open Polynomial SchwarzschildLaurent NumeratorData ExactRational MetricBare

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

private theorem exprPow_value (k ell : ℂ) (a : Expr) (n : ℕ) :
    Expr.value k ell (exprPow a n) = (Expr.value k ell a)^n := by
  induction n with
  | zero => simp [exprPow, c, Expr.value_constant]
  | succ n ih => rw [exprPow, Expr.value_mul, ih, pow_succ]

private theorem parent_gap_value (k ell : ℂ) :
    Expr.value k ell Factor.parentGap.data = C (12*(k+gamma ell)) := by
  simp only [Factor.data, l, w, Expr.value_add, Expr.value_mul, Expr.value_sub,
    Expr.value_constant, Expr.value_angular, Expr.value_frequency, ← map_add, ← map_mul,
    ← map_sub, Int.cast_ofNat, Int.cast_one]
  congr 1
  unfold gamma
  ring

private theorem daughter_gap_value (k ell : ℂ) :
    Expr.value k ell (Expr.neg Factor.daughterGap.data) = C (6*(k-daughterGamma ell)) := by
  simp only [Factor.data, u, l, w, c, Expr.value_neg, Expr.value_add, Expr.value_mul,
    Expr.value_sub, Expr.value_constant, Expr.value_angular, Expr.value_frequency,
    ← map_neg, ← map_add, ← map_mul, ← map_sub, Int.cast_ofNat, Int.cast_one]
  congr 1
  unfold daughterGamma gamma
  ring

private theorem metric_scalar_value (multiplier : ℕ) (second : Bool) (k ell : ℂ) :
    Expr.value k ell (metricScalar multiplier second) = C (fieldScalar multiplier second k ell) := by
  cases second <;>
    simp only [metricScalar, fieldScalar, exprPow_value, Expr.value_mul, parent_gap_value,
      daughter_gap_value, Bool.false_eq_true, if_false, if_true] <;>
    simp only [Factor.data, u, l, w, c, Expr.value_constant, Expr.value_angular,
      Expr.value_frequency, Expr.value_add, Expr.value_sub, Expr.value_mul, exprPow_value,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat, ← map_add, ← map_sub, ← map_mul, ← map_pow]

theorem metric_denominator_value (m : ℕ) (second : Bool) (k ell : ℂ) :
    Expr.value k ell (metricSourceDenominator m second) =
      denominatorStep (poles ell) *
        (denominatorStep (poles ell) * fieldDenominator (fieldScalar m second k ell) ell) := by
  simp [metricSourceDenominator, metric_scalar_value, denominatorStep, fieldDenominator,
    xh, shiftedRadius, x_value, c, Expr.value_constant, exprPow_value,
    parentPole_value, daughterPole_value, poles_value]

theorem checked_row_value (k ell : ℂ) (a b : ExprRow)
    (c₀ : Expr.Check a.1 b.1) (c₁ : Expr.Check a.2.1 b.2.1) (c₂ : Expr.Check a.2.2 b.2.2) :
    rowValue k ell a = rowValue k ell b :=
  Prod.ext (Expr.value_eq_of_check _ _ c₀ k ell)
    (Prod.ext (Expr.value_eq_of_check _ _ c₁ k ell) (Expr.value_eq_of_check _ _ c₂ k ell))

private theorem sub_value (k ell : ℂ) (p q : ExprRow) :
    rowValue k ell (subData p q) = minus (rowValue k ell p) (rowValue k ell q) := by
  simp [rowValue, subData, mapRow, minus]

theorem split_metric_image (k ell : ℂ) (field intermediate secondStep source : ExprRow)
    (step : rowValue k ell (stepData 13 6 2 intermediate) = rowValue k ell secondStep)
    (finish : rowValue k ell (metricFinish field secondStep) = rowValue k ell source) :
    rowValue k ell (metricSecondStep field intermediate) = rowValue k ell source := by
  rw [metricSecondStep, sub_value, step, ← sub_value]
  exact finish

theorem checked_bare_field (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (m : ℕ) (hm : 0 < m) (second : Bool) (field intermediate source : ExprRow)
    (a b c : Fraction)
    (stepA : Expr.Check (stepData 11 5 1 field).1 intermediate.1)
    (stepB : Expr.Check (stepData 11 5 1 field).2.1 intermediate.2.1)
    (stepC : Expr.Check (stepData 11 5 1 field).2.2 intermediate.2.2)
    (image : rowValue k n (metricSecondStep field intermediate) = rowValue k n source)
    (fa : Cancellation ⟨source.1, metricSourceDenominator m second⟩ a)
    (fb : Cancellation ⟨source.2.1, metricSourceDenominator m second⟩ b)
    (fc : Cancellation ⟨source.2.2, metricSourceDenominator m second⟩ c) :
    rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (localField field m second k n) =
      (a.value k n, b.value k n, c.value k n) := by
  have hs := fieldScalar_ne_zero m n hm hn second k hk ki
  have hstep : denominatorStep (poles (n:ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (poles_ne_zero n hn)
  have hz : ι (Expr.value k n (metricSourceDenominator m second)) ≠ 0 := by
    rw [metric_denominator_value]
    exact RatFunc.algebraMap_ne_zero
      (mul_ne_zero hstep (mul_ne_zero hstep (fieldDenominator_ne_zero _ hs n hn)))
  have first := checked_row_value k n (stepData 11 5 1 field) intermediate stepA stepB stepC
  have step :
      rowValue k n (stepData 13 6 2 (stepData 11 5 1 field)) =
        rowValue k n (stepData 13 6 2 intermediate) := by
    rw [step_value k n 13 6 2 (stepData 11 5 1 field), step_value k n 13 6 2 intermediate, first]
  have checked : rowValue k n (sourceData field) = rowValue k n source := by
    rw [sourceData, sub_value, step, ← sub_value]
    exact image
  have equation :
      rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (localField field m second k n) =
        projectedSource source m second k n :=
    source_of_checked_numerators k n _ field source (fieldDenominator_ne_zero _ hs n hn)
      (poles_ne_zero n hn) checked
  rw [equation]
  have link (f : Expr) (out : Fraction) (check : Cancellation ⟨f, metricSourceDenominator m second⟩ out) :=
    (check.sound k n hz).1
  unfold projectedSource
  have ha := link source.1 a fa
  have hb := link source.2.1 b fb
  have hc := link source.2.2 c fc
  simp only [Fraction.value, metric_denominator_value] at ha hb hc
  exact Prod.ext ha.symm (Prod.ext hb.symm hc.symm)

#print axioms checked_bare_field

end
end SchwarzschildMixtures
