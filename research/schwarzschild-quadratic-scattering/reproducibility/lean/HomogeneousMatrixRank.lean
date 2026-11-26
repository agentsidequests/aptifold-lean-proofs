import HomogeneousMatrixData

/-! Coordinate projections for the homogeneous Laurent matrix. -/
namespace SchwarzschildMatrix

def homogeneousColumns : List (Nat × Int) :=
  ((List.range 8).map fun (i : Nat) => (0, (i : Int) - 7)) ++
  ((List.range 6).map fun (i : Nat) => (1, (i : Int) - 7)) ++
  ((List.range 4).map fun (i : Nat) => (2, (i : Int) - 7))

private def homogeneousColumn (i : Nat) : Nat × Int :=
  (homogeneousColumns[i]?).getD (0, 0)

private def homogeneousWeight (i row : Nat) : Polynomial :=
  ((homogeneousWeights[i]?).getD #[])[row]?.getD []

private def verifiesProjection (i : Nat) : Bool :=
  homogeneousColumns.all fun col =>
    coordinateProjectionMatches homogeneousRowIndices (homogeneousWeight i) col
      (if col = homogeneousColumn i then homogeneousTarget else [])

set_option maxRecDepth 12000
set_option maxHeartbeats 10000000

private theorem projection00 : verifiesProjection 0 = true := by decide +kernel
private theorem projection01 : verifiesProjection 1 = true := by decide +kernel
private theorem projection02 : verifiesProjection 2 = true := by decide +kernel
private theorem projection03 : verifiesProjection 3 = true := by decide +kernel
private theorem projection04 : verifiesProjection 4 = true := by decide +kernel
private theorem projection05 : verifiesProjection 5 = true := by decide +kernel
private theorem projection06 : verifiesProjection 6 = true := by decide +kernel
private theorem projection07 : verifiesProjection 7 = true := by decide +kernel
private theorem projection08 : verifiesProjection 8 = true := by decide +kernel
private theorem projection09 : verifiesProjection 9 = true := by decide +kernel
private theorem projection10 : verifiesProjection 10 = true := by decide +kernel
private theorem projection11 : verifiesProjection 11 = true := by decide +kernel
private theorem projection12 : verifiesProjection 12 = true := by decide +kernel
private theorem projection13 : verifiesProjection 13 = true := by decide +kernel
private theorem projection14 : verifiesProjection 14 = true := by decide +kernel
private theorem projection15 : verifiesProjection 15 = true := by decide +kernel
private theorem projection16 : verifiesProjection 16 = true := by decide +kernel
private theorem projection17 : verifiesProjection 17 = true := by decide +kernel

private theorem allProjections : (List.range 18).all verifiesProjection = true := by
  rw [show List.range 18 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from (by decide +kernel)]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    projection00, projection01, projection02, projection03, projection04, projection05,
    projection06, projection07, projection08, projection09, projection10, projection11,
    projection12, projection13, projection14, projection15, projection16, projection17]

theorem homogeneous_rows_valid (i : Nat) (hi : i ∈ homogeneousRowIndices) : i ∈ rows := by
  have all : homogeneousRowIndices.all (fun r => decide (r ∈ rows)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i hi)

open Lean.Grind

/-- The checked row combinations recover every retained coordinate up to a common factor. -/
theorem homogeneous_coordinate_certificate {K : Type u} [Field K] (k ell : K)
    (x : (Nat × Int) → K)
    (support : ∀ col ∈ columnLabels, col ∉ homogeneousColumns → x col = 0)
    (equations : ∀ i ∈ rows, matrixApply k ell x i = 0)
    (col : Nat × Int) (hc : col ∈ homogeneousColumns) :
    evalPoly k ell homogeneousTarget * x col = 0 := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
  have size : homogeneousColumns.length = 18 := by decide +kernel
  have hr : i ∈ List.range 18 := List.mem_range.mpr (size ▸ hi)
  have identity : homogeneousColumn i = col := by
    simpa only [homogeneousColumn, List.getElem?_eq_getElem hi, Option.getD_some] using he
  have check := List.all_eq_true.mp allProjections i hr
  unfold verifiesProjection at check
  rw [identity] at check
  have subset : homogeneousColumns.all (fun c => decide (c ∈ columnLabels)) = true := by decide +kernel
  have member := _root_.of_decide_eq_true (List.all_eq_true.mp subset col hc)
  exact coordinate_from_kernel_projection homogeneousRowIndices homogeneousColumns
    (homogeneousWeight i) col homogeneousTarget member k ell x support
    (fun j hj => equations j (homogeneous_rows_valid j hj)) check hc

#print axioms homogeneous_coordinate_certificate

end SchwarzschildMatrix
