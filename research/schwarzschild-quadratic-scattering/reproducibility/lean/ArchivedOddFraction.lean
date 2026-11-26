import ArchivedOddData
import ArchivedRationalSource
import AdmittedMixtureNumerators

/-! Identify the computational numerator with the actual pole-subtracted
source used by the matrix exclusion. -/
namespace SchwarzschildMixtures
namespace ArchivedOddData

open Polynomial SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def matrixDenominator (k ell : ℂ) : ℂ[X] :=
  C (SchwarzschildMatrix.sourceClearance k ell) * X^6

private theorem value_coefficients (k ell : ℂ) (ps : List Poly) :
    Expr.value k ell (.coefficients ps) = (ps.map (Poly.value k ell)).sum := by
  change Poly.value k ell ps.flatten = _
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatten_cons, List.map_cons, List.sum_cons, Poly.value_append, ih]

private theorem monomial_table_value (k ell : ℂ) (d : ℕ) (ts : List SchwarzschildMatrix.Monomial) :
    Poly.value k ell (ts.map fun t => ⟨d,t.1,t.2.1,t.2.2⟩) =
      monomial d (SchwarzschildMatrix.total ts (SchwarzschildMatrix.evalMonomial k ell)) := by
  induction ts with
  | nil => simp [Poly.value, SchwarzschildMatrix.total]
  | cons t ts ih =>
    simp only [List.map_cons, Poly.value, Poly.termValue, ih, SchwarzschildMatrix.total,
      List.foldr_cons, SchwarzschildMatrix.evalMonomial, map_add, C_mul_X_pow_eq_monomial]

private theorem shift_bound (i : ℕ) (hi : i < 41)
    (hne : SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource i ≠ []) :
    0 ≤ (rowLabel i).2+6 := by
  have checked : SchwarzschildMatrix.rows.all (fun j => decide
      (SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource j = [] ∨
        0 ≤ (rowLabel j).2 + 6)) = true := by decide +kernel
  have h := List.all_eq_true.mp checked i (by simpa [SchwarzschildMatrix.rows] using hi)
  exact (of_decide_eq_true h).resolve_left hne

private theorem table_term_fraction (k ell : ℂ) (j i : ℕ) (hi : i < 41) :
    laurentToRat (AddMonoidAlgebra.single (rowLabel i).2 (archivedWeight k ell j i)) =
      ι (Poly.value k ell (tableTerms j i)) / ι (matrixDenominator k ell) := by
  have eq : tableLabel i = rowLabel i := rfl
  by_cases hj : (rowLabel i).1 = j
  · simp only [tableTerms, eq, hj, if_true]
    change laurentToRat _ =
      ι (Poly.value k ell ((SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource i).map _)) / _
    rw [monomial_table_value]
    by_cases he : SchwarzschildMatrix.termsAt SchwarzschildMatrix.clearedSource i = []
    · simp [he, archivedWeight, hj, SchwarzschildMatrix.sourceEntry,
        SchwarzschildMatrix.clearedSourceEntry, SchwarzschildMatrix.total]
    · rw [laurentToRat_monomial_fraction _ _ 6 (shift_bound i hi he)]
      simp only [archivedWeight, hj, if_true, SchwarzschildMatrix.sourceEntry,
        SchwarzschildMatrix.clearedSourceEntry, matrixDenominator, ← C_mul_X_pow_eq_monomial,
        map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_div₀]
      field_simp [RatFunc.X_ne_zero]
      norm_num
  · simp [archivedWeight, tableTerms, eq, hj, Poly.value]

private theorem component_fraction (k ell : ℂ) (j : ℕ) :
    laurentToRat (archivedComponent k ell j) =
      ι (Expr.value k ell (tableComponent j)) / ι (matrixDenominator k ell) := by
  rw [archivedComponent, map_sum, tableComponent, value_coefficients, List.map_ofFn, List.sum_ofFn]
  change (∑ i ∈ Finset.range 41, _) = ι (∑ i : Fin 41, Poly.value k ell (tableTerms j (i:ℕ))) / _
  rw [Fin.sum_univ_eq_sum_range (fun i => Poly.value k ell (tableTerms j i)) 41, map_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi => table_term_fraction k ell j i (Finset.mem_range.mp hi)

theorem archived_source_as_fraction (k ell : ℂ) :
    archivedSource k ell =
      fractionRow (rowValue k ell tableNumerators) (matrixDenominator k ell) := by
  simp only [archivedSource, archivedLaurentSource, mapRow, fractionRow, rowValue, tableNumerators]
  exact Prod.ext (component_fraction k ell 0)
    (Prod.ext (component_fraction k ell 1) (component_fraction k ell 2))

#print axioms archived_source_as_fraction

end
end ArchivedOddData
end SchwarzschildMixtures
