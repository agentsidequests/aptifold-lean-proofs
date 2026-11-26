import PureOddEvaluation
import PureOddWitness
import OddBareChecks
import RegularizedOddSource
import RationalRowExclusion

/-! The calculated, unregularized odd–odd source is the archived
obstruction plus the operator applied to the removed pole terms. -/
namespace SchwarzschildMixtures.PureOddProgram

open Polynomial SchwarzschildLaurent ExactRational

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative

private theorem matrix_denominator_data (k ell : ℂ) :
    Expr.value k ell matrixDenominatorData = ArchivedOddData.matrixDenominator k ell := by
  have clearance : SchwarzschildMatrix.sourceClearance k ell =
      (SchwarzschildMatrix.sourceScale : ℂ)*(2*ell+1)*(2*ell-1)*(ell+1)*
        (-(ell*(ell+1)*(2*ell-1)*(2*ell+1)-6*k)) := by
    rw [matrix_clearance_value]
    unfold daughterGamma gamma
    ring
  have radius_power : Expr.value k ell (NumeratorData.x 6) = (X : ℂ[X])^6 := by
    simp [NumeratorData.x, Expr.value_single]
  rw [ArchivedOddData.matrixDenominator, clearance]
  simp only [matrixDenominatorData, Factor.data, NumeratorData.c, radius_power,
    NumeratorData.l, NumeratorData.w, NumeratorData.u, Expr.value_add, Expr.value_sub,
    Expr.value_mul, Expr.value_neg, Expr.value_frequency, Expr.value_angular, Expr.value_constant,
    ← map_mul, ← map_add, ← map_sub, ← map_neg, Int.cast_ofNat, Int.cast_one]

private theorem source_denominator (m : ℕ) (k ell : ℂ) :
    Expr.value k ell (sourceDenominatorData m) =
      denominatorStep (poles ell) *
        (denominatorStep (poles ell) * fieldDenominator (fieldScalar (oddMultiplier m) false k ell) ell) := by
  rw [sourceDenominatorData, Expr.value_mul, matrix_denominator_data, padded_denominator]

private theorem archive_row_value (m : ℕ) (k ell : ℂ)
    (source : Row Expr) (output : SchwarzschildEinstein.PureOdd.Quadratic Fraction)
    (hd : ι (Expr.value k ell (sourceDenominatorData m)) ≠ 0)
    (a : Cancellation ⟨source.1, sourceDenominatorData m⟩ output.1)
    (b : Cancellation ⟨source.2.1, sourceDenominatorData m⟩ output.2.1)
    (c : Cancellation ⟨source.2.2, sourceDenominatorData m⟩ output.2.2) :
    SchwarzschildEinstein.PureOdd.mapRow (Fraction.value k ell) output = oddForcing m source k ell := by
  have first := (a.sound k ell hd).1
  have second := (b.sound k ell hd).1
  have third := (c.sound k ell hd).1
  simp only [Fraction.value, source_denominator] at first second third
  exact Prod.ext first (Prod.ext second third)

attribute [local irreducible] OddBareCase.sourceA OddBareCase.sourceB OddBareCase.sourceC

private theorem arithmetic_to_odd_forcing (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    SchwarzschildEinstein.PureOdd.bareForcing δ R (Cᵣ k) (Cᵣ (n:ℂ)) =
      oddForcing OddBareCase.multiplier OddBareCase.forcing k n := by
  have hscale : (0 : ℕ) < oddMultiplier OddBareCase.multiplier := by decide +kernel
  have hfield := fieldDenominator_ne_zero _
    (fieldScalar_ne_zero _ n hscale hn false k hk ki) n hn
  have hder : denominatorStep (poles (n:ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (poles_ne_zero n hn)
  have hd : ι (Expr.value k n (sourceDenominatorData OddBareCase.multiplier)) ≠ 0 := by
    rw [source_denominator]
    exact RatFunc.algebraMap_ne_zero (mul_ne_zero hder (mul_ne_zero hder hfield))
  exact (certified_radial_coefficients n hn k ki PureOddWitness.coefficients
    PureOddWitness.a_reduced PureOddWitness.b_reduced PureOddWitness.c_reduced).trans
      (archive_row_value OddBareCase.multiplier k n OddBareCase.forcing PureOddWitness.coefficients
        hd OddBareCase.a_same OddBareCase.b_same OddBareCase.c_same)

set_option maxRecDepth 4200 in
theorem calculated_odd_source_is_archived (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    SchwarzschildEinstein.PureOdd.bareForcing δ R (Cᵣ k) (Cᵣ (n:ℂ)) =
      plus (rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k
        (oddShift OddBareCase.multiplier OddBareCase.field k n)) (archivedSource k n) := by
  rw [arithmetic_to_odd_forcing n hn k hk ki]
  exact odd_forcing_restored OddBareCase.multiplier n (by decide +kernel) hn k hk ki
    OddBareCase.field OddBareCase.forcing OddBareCase.odd_a_checked OddBareCase.odd_b_checked
    OddBareCase.odd_c_checked

theorem calculated_pure_odd_has_no_particular (n : ℕ) (hn : 2 ≤ n) (k : ℂ)
    (hk : k ≠ 0) (ki : k.re = 0) :
    ¬ ∃ p : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k p =
      SchwarzschildEinstein.PureOdd.bareForcing δ R (Cᵣ k) (Cᵣ (n:ℂ)) := by
  rintro ⟨p, hp⟩
  let shift := oddShift OddBareCase.multiplier OddBareCase.field k n
  have excludes : ¬ ∃ p : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k p =
      archivedSource k n := by
    simpa only [Int.cast_natCast] using archived_rational_row_no_solution n hn k hk ki
  refine excludes ⟨minus p shift, ?_⟩
  rw [operator_minus, hp, calculated_odd_source_is_archived n hn k hk ki]
  apply Prod.ext
  · simp [shift, minus, plus]
  · apply Prod.ext <;> simp [shift, minus, plus]

#print axioms calculated_odd_source_is_archived
#print axioms calculated_pure_odd_has_no_particular

end
end SchwarzschildMixtures.PureOddProgram
