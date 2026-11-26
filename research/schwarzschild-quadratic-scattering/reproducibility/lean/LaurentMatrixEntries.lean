import LaurentMatrixOperator

/-! The archived matrix entries are coefficients of exact Laurent rows. -/
namespace SchwarzschildLaurent

noncomputable section

def rowComponent {A : Type*} (j : ℕ) (u : Row A) : A :=
  match j with
  | 0 => u.1
  | 1 => u.2.1
  | _ => u.2.2

theorem rowComponent_map {A B : Type*} (g : A → B) (j : ℕ) (u : Row A) :
    rowComponent j (mapRow g u) = g (rowComponent j u) := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

theorem rowComponent_plus {A : Type*} [Add A] (j : ℕ) (u v : Row A) :
    rowComponent j (plus u v) = rowComponent j u + rowComponent j v := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

theorem rowComponent_scale {A : Type*} [Mul A] (j : ℕ) (s : A) (u : Row A) :
    rowComponent j (scale s u) = s * rowComponent j u := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

theorem rowComponent_zero {A : Type*} [Zero A] (j : ℕ) : rowComponent j (0 : Row A) = 0 := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

private theorem evaluate_insert (k ell : ℂ) (t : SchwarzschildMatrix.Monomial)
    (p : List SchwarzschildMatrix.Monomial) :
    SchwarzschildMatrix.total (SchwarzschildMatrix.insertMonomial t p) (SchwarzschildMatrix.evalMonomial k ell) =
      SchwarzschildMatrix.evalMonomial k ell t + SchwarzschildMatrix.total p (SchwarzschildMatrix.evalMonomial k ell) := by
  induction p with
  | nil => rfl
  | cons u p ih =>
    simp only [SchwarzschildMatrix.insertMonomial, Bool.and_eq_true, beq_iff_eq]
    split
    next h =>
      simp only [SchwarzschildMatrix.total, List.foldr_cons, SchwarzschildMatrix.evalMonomial,
        ← h.1, ← h.2, Int.cast_add, add_mul]
      ring
    next _ =>
      change SchwarzschildMatrix.evalMonomial k ell u +
        SchwarzschildMatrix.total (SchwarzschildMatrix.insertMonomial t p) (SchwarzschildMatrix.evalMonomial k ell) =
        SchwarzschildMatrix.evalMonomial k ell t +
          (SchwarzschildMatrix.evalMonomial k ell u + SchwarzschildMatrix.total p (SchwarzschildMatrix.evalMonomial k ell))
      rw [ih]
      abel

private theorem evaluate_drop_zero (k ell : ℂ) (p : List SchwarzschildMatrix.Monomial) :
    SchwarzschildMatrix.total (p.filter fun t => t.2.2 != 0) (SchwarzschildMatrix.evalMonomial k ell) =
      SchwarzschildMatrix.total p (SchwarzschildMatrix.evalMonomial k ell) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases h : t.2.2 = 0
    · simpa [List.filter_cons, SchwarzschildMatrix.total, SchwarzschildMatrix.evalMonomial, h] using ih
    · simpa [List.filter_cons, SchwarzschildMatrix.total, h] using congrArg
        (fun z => SchwarzschildMatrix.evalMonomial k ell t + z) ih

private def collectRadius (m : ℤ) (p : SchwarzschildMatrix.Laurent) : List SchwarzschildMatrix.Monomial :=
  p.foldr (fun t acc => if t.radius == m then
    SchwarzschildMatrix.insertMonomial (t.frequency, t.angular, t.coefficient) acc else acc) []

private theorem evaluate_collect (k ell : ℂ) (m : ℤ) (p : SchwarzschildMatrix.Laurent) :
    SchwarzschildMatrix.total (collectRadius m p) (SchwarzschildMatrix.evalMonomial k ell) =
      (matrixListValue k ell p).coeff m := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [collectRadius, beq_iff_eq] at ih
    simp only [collectRadius, List.foldr_cons, matrixListValue, matrixTermValue, AddMonoidAlgebra.coeff_add,
      AddMonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.single_apply, beq_iff_eq]
    by_cases h : t.radius = m
    · simp only [h, if_true, evaluate_insert, ih]
    · simp only [h, if_false, zero_add, ih]

theorem coefficient_correct (k ell : ℂ) (u : SchwarzschildMatrix.LaurentRow) (label : ℕ × ℤ) :
    SchwarzschildMatrix.total (SchwarzschildMatrix.coefficient u label) (SchwarzschildMatrix.evalMonomial k ell) =
      (matrixListValue k ell (rowComponent label.1 u)).coeff label.2 := by
  change SchwarzschildMatrix.total ((collectRadius label.2 (rowComponent label.1 u)).filter
    fun t => t.2.2 != 0) (SchwarzschildMatrix.evalMonomial k ell) = _
  rw [evaluate_drop_zero, evaluate_collect]

def matrixBasis (label : ℕ × ℤ) : SchwarzschildMatrix.LaurentRow :=
  let t : SchwarzschildMatrix.Laurent := [⟨label.2, 0, 0, 1⟩]
  match label.1 with
  | 0 => (t, [], [])
  | 1 => ([], t, [])
  | _ => ([], [], t)

def matrixBasisImage (k ell : ℂ) (label : ℕ × ℤ) : Row LPoly :=
  mapRow (matrixListValue k ell) (SchwarzschildMatrix.operator (matrixBasis label))

theorem matrixEntry_correct (k ell : ℂ) (label : ℕ × ℤ) (i : ℕ) (hi : i < 41) :
    (rowComponent (rowLabel i).1 (matrixBasisImage k ell label)).coeff (rowLabel i).2 =
      SchwarzschildMatrix.matrixEntry k ell label i := by
  change _ = SchwarzschildMatrix.total (SchwarzschildMatrix.termsAt
    (SchwarzschildMatrix.rowLabels.map (SchwarzschildMatrix.coefficient
      (SchwarzschildMatrix.operator (matrixBasis label)))) i) _
  have hlen : SchwarzschildMatrix.rowLabels.length = 41 := by decide +kernel
  have hi' : i < SchwarzschildMatrix.rowLabels.length := by omega
  simp only [SchwarzschildMatrix.termsAt, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, ← rowLabel_eq hi]
  rw [coefficient_correct, matrixBasisImage, rowComponent_map]

theorem sourceEntry_correct (k ell : ℂ) (i : ℕ) (hi : i < 41) :
    (rowComponent (rowLabel i).1 (archivedLaurentSource k ell)).coeff (rowLabel i).2 =
      SchwarzschildMatrix.sourceEntry k ell i := by
  have bound := rowLabel_component i hi
  have sel (j : ℕ) (hj : j ≤ 2) : rowComponent j (archivedLaurentSource k ell) = archivedComponent k ell j := by
    have cases : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl
  rw [sel _ bound, archivedComponent_coeff k ell i hi]

#print axioms coefficient_correct
#print axioms matrixEntry_correct
#print axioms sourceEntry_correct

end

end SchwarzschildLaurent
