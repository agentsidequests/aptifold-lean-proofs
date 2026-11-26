import LaurentMatrixEntries

/-! The pole-subtracted odd-source equation has no rational row solution. -/
namespace SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private theorem plus_zero_row {A : Type*} [AddMonoid A] (u : Row A) : plus u 0 = u := by
  simp [plus]

private theorem mapRow_zero {A B : Type*} [Semiring A] [Semiring B] (g : A →+* B) :
    mapRow g (0 : Row A) = 0 := by simp [mapRow]

private theorem mapRow_injective {A B : Type*} {g : A → B} (hg : Function.Injective g) :
    Function.Injective (mapRow g) := by
  intro u v e
  exact Prod.ext (hg (congrArg Prod.fst e))
    (Prod.ext (hg (congrArg (fun r => r.2.1) e)) (hg (congrArg (fun r => r.2.2) e)))

private def combination {A : Type*} [Semiring A] (p : (ℕ × ℤ) → Row A) (w : (ℕ × ℤ) → A) :
    List (ℕ × ℤ) → Row A
  | [] => 0
  | l :: ls => plus (scale (w l) (p l)) (combination p w ls)

private theorem combination_append {A : Type*} [Semiring A]
    (p : (ℕ × ℤ) → Row A) (w : (ℕ × ℤ) → A) (l r : List (ℕ × ℤ)) :
    combination p w (l ++ r) = plus (combination p w l) (combination p w r) := by
  induction l with
  | nil => simp [combination, plus]
  | cons a l ih => simp [combination, ih, plus, add_assoc]

private theorem combination_map {A B : Type*} [Semiring A] [Semiring B] (g : A →+* B)
    (p : (ℕ × ℤ) → Row A) (w : (ℕ × ℤ) → A) (ls : List (ℕ × ℤ)) :
    mapRow g (combination p w ls) = combination (fun l => mapRow g (p l)) (fun l => g (w l)) ls := by
  induction ls with
  | nil => exact mapRow_zero g
  | cons l ls ih => simp only [combination, mapRow_plus, mapRow_scale, ih]

private def componentBasis {A : Type*} [Zero A] (j : ℕ) (x : A) : Row A :=
  match j with
  | 0 => (x, 0, 0)
  | 1 => (0, x, 0)
  | _ => (0, 0, x)

private theorem componentBasis_plus {A : Type*} [AddMonoid A] (j : ℕ) (a b : A) :
    componentBasis j (a+b) = plus (componentBasis j a) (componentBasis j b) := by
  cases j with
  | zero => simp [componentBasis, plus]
  | succ j => cases j <;> simp [componentBasis, plus]

private theorem componentBasis_scale {A : Type*} [Semiring A] (j : ℕ) (a b : A) :
    componentBasis j (a*b) = scale a (componentBasis j b) := by
  cases j with
  | zero => simp [componentBasis, scale]
  | succ j => cases j <;> simp [componentBasis, scale]

private theorem componentBasis_zero {A : Type*} [Zero A] (j : ℕ) : componentBasis j (0:A) = 0 := by
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

private def basisRat (c : ℕ × ℤ) : Row ℂᵣ := componentBasis c.1 (R^c.2)

private theorem matrixBasisRat_correct (k ell : ℂ) (c : ℕ × ℤ) :
    mapRow (matrixListRat k ell) (matrixBasis c) = basisRat c := by
  have val (m : ℤ) : matrixListRat k ell [⟨m,0,0,1⟩] = R^m := by
    change laurentToRat (AddMonoidAlgebra.single m (SchwarzschildMatrix.evalMonomial k ell (0,0,1))+0) = _
    rw [add_zero, laurentToRat_single]
    simp [SchwarzschildMatrix.evalMonomial]
  rcases c with ⟨j,m⟩
  cases j with
  | zero => simp [matrixBasis, basisRat, componentBasis, mapRow, val, matrixListRat_nil]
  | succ j => cases j <;> simp [matrixBasis, basisRat, componentBasis, mapRow, val, matrixListRat_nil]

private theorem matrixBasisImageRat_correct (k ell : ℂ) (c : ℕ × ℤ) :
    mapRow laurentToRat (matrixBasisImage k ell c) =
      rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k (basisRat c) := by
  change mapRow (matrixListRat k ell) (SchwarzschildMatrix.operator (matrixBasis c)) = _
  rw [matrix_operator_correct, matrixBasisRat_correct]

def columnWeights (a : Row (ℕ → ℂ)) (c : ℕ × ℤ) : ℂ :=
  rowComponent c.1 a (c.2+7).toNat

private theorem combination_span (a : Row (ℕ → ℂ)) (j count : ℕ) :
    combination basisRat (fun c => Cᵣ (columnWeights a c))
      ((List.range count).map (fun (i : ℕ) => (j, (i:ℤ)-7))) =
      componentBasis j (laurentSpan count (rowComponent j a)) := by
  induction count with
  | zero => simp [combination, laurentSpan, componentBasis_zero]
  | succ n ih =>
    rw [List.range_succ, List.map_append, combination_append, ih]
    simp only [List.map_cons, List.map_nil, combination, plus_zero_row, basisRat, columnWeights,
      laurentSpan, Finset.sum_range_succ, componentBasis_plus, componentBasis_scale]
    have hn : ((n:ℤ)-7+7).toNat = n := by omega
    rw [hn]

private theorem combination_input (a : Row (ℕ → ℂ)) :
    combination basisRat (fun c => Cᵣ (columnWeights a c)) SchwarzschildMatrix.columnLabels =
      (laurentSpan 12 a.1, laurentSpan 10 a.2.1, laurentSpan 8 a.2.2) := by
  simp [SchwarzschildMatrix.columnLabels, combination_append, combination_span, rowComponent, componentBasis, plus]

private theorem jet_plus (a b c : ℂᵣ) (u v : Row ℂᵣ) :
    jet a b c (plus u v) = plus (jet a b c u) (jet a b c v) := by
  apply Prod.ext
  · simp [jet, plus, mul_add]
  · apply Prod.ext <;> simp only [jet, plus] <;> ring

private theorem step_plus (h k : ℂ) (u v : Row ℂᵣ) :
    rationalStep h k (plus u v) = plus (rationalStep h k u) (rationalStep h k v) := by
  simp only [rationalStep, rationalRowDerivative_plus, jet_plus, scale_plus]
  apply Prod.ext
  · simp only [plus]; abel
  · apply Prod.ext <;> simp only [plus] <;> abel

private theorem step_constant_scale (h k c : ℂ) (u : Row ℂᵣ) :
    rationalStep h k (scale (Cᵣ c) u) = scale (Cᵣ c) (rationalStep h k u) := by
  simp only [rationalStep, rationalRowDerivative_scale, rationalDerivative_constant, zero_scale_row,
    jet_scale, scale_plus, scale_scale]
  have z (v : Row ℂᵣ) : plus 0 v = v := by simp [plus]
  rw [scale_zero_row, z, mul_comm radialFactor]

theorem operator_plus (h hD k : ℂ) (u v : Row ℂᵣ) :
    rationalOperator h hD k (plus u v) = plus (rationalOperator h hD k u) (rationalOperator h hD k v) := by
  simp only [rationalOperator, step_plus, scale_plus]
  apply Prod.ext
  · simp only [plus, minus]; abel
  · apply Prod.ext <;> simp only [plus, minus] <;> abel

theorem operator_constant_scale (h hD k c : ℂ) (u : Row ℂᵣ) :
    rationalOperator h hD k (scale (Cᵣ c) u) = scale (Cᵣ c) (rationalOperator h hD k u) := by
  simp only [rationalOperator, step_constant_scale, scale_minus, scale_scale]
  rw [mul_comm (Cᵣ (4*k^2) + oddPotential hD)]

theorem operator_minus (h hD k : ℂ) (u v : Row ℂᵣ) :
    rationalOperator h hD k (minus u v) =
      minus (rationalOperator h hD k u) (rationalOperator h hD k v) := by
  have to_plus (p q : Row ℂᵣ) : minus p q = plus p (scale (Cᵣ (-1)) q) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [minus, plus, scale, sub_eq_add_neg]
  rw [to_plus, operator_plus, operator_constant_scale, ← to_plus]

private theorem operator_zero (h hD k : ℂ) : rationalOperator h hD k 0 = 0 := by
  simpa only [map_zero, zero_scale_row] using operator_constant_scale h hD k 0 0

private theorem operator_combination (h hD k : ℂ) (x : (ℕ × ℤ) → ℂ) (cols : List (ℕ × ℤ)) :
    rationalOperator h hD k (combination basisRat (fun c => Cᵣ (x c)) cols) =
      combination (fun c => rationalOperator h hD k (basisRat c)) (fun c => Cᵣ (x c)) cols := by
  induction cols with
  | nil => exact operator_zero h hD k
  | cons c cols ih => simp only [combination, operator_plus, operator_constant_scale, ih]

private theorem combination_coeff (k ell : ℂ) (x : (ℕ × ℤ) → ℂ) (cols : List (ℕ × ℤ))
    (i : ℕ) (hi : i < 41) :
    (rowComponent (rowLabel i).1 (combination (matrixBasisImage k ell)
      (fun c => LaurentPolynomial.C (x c)) cols)).coeff (rowLabel i).2 =
      SchwarzschildMatrix.total cols (fun c => SchwarzschildMatrix.matrixEntry k ell c i * x c) := by
  induction cols with
  | nil =>
    simp only [combination, rowComponent_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      SchwarzschildMatrix.total, List.foldr_nil]
  | cons c cols ih =>
    simp only [combination, rowComponent_plus, rowComponent_scale, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih, SchwarzschildMatrix.total, List.foldr_cons]
    rw [← LaurentPolynomial.smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      matrixEntry_correct k ell c i hi, mul_comm (x c)]

private theorem span_matrix_equations (k ell : ℂ) (a : Row (ℕ → ℂ)) (s : Row LPoly)
    (eq : rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k
      (laurentSpan 12 a.1, laurentSpan 10 a.2.1, laurentSpan 8 a.2.2) = mapRow laurentToRat s) :
    ∀ i ∈ SchwarzschildMatrix.rows, SchwarzschildMatrix.matrixApply k ell (columnWeights a) i =
      (rowComponent (rowLabel i).1 s).coeff (rowLabel i).2 := by
  have e : combination (matrixBasisImage k ell) (fun c => LaurentPolynomial.C (columnWeights a c))
      SchwarzschildMatrix.columnLabels = s := by
    apply mapRow_injective laurentToRat_injective
    rw [combination_map]
    simp only [laurentToRat, LaurentPolynomial.eval₂_C]
    change combination (fun c => mapRow laurentToRat (matrixBasisImage k ell c))
      (fun c => Cᵣ (columnWeights a c)) SchwarzschildMatrix.columnLabels = mapRow laurentToRat s
    rw [show (fun c => mapRow laurentToRat (matrixBasisImage k ell c)) =
      (fun c => rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k (basisRat c))
      from funext (matrixBasisImageRat_correct k ell)]
    rw [← operator_combination, combination_input, eq]
  intro i hm
  have hr : i < 41 := by simpa [SchwarzschildMatrix.rows] using hm
  have he := congrArg (fun r => (rowComponent (rowLabel i).1 r).coeff (rowLabel i).2) e
  rwa [combination_coeff k ell _ _ i hr] at he

/-- The rational equation implies the actual 41 equations of the existing matrix certificate. -/
theorem matrix_equations_from_rational_solution (k ell : ℂ) (hk : k ≠ 0) (hi : k.re = 0) (u : Row ℂᵣ)
    (eq : rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k u = archivedSource k ell) :
    ∃ x : (ℕ × ℤ) → ℂ, ∀ i ∈ SchwarzschildMatrix.rows,
      SchwarzschildMatrix.matrixApply k ell x i = SchwarzschildMatrix.sourceEntry k ell i := by
  obtain ⟨a, ha⟩ := matrix_span_from_rational_row _ _ k hk hi u _ eq (archivedSource_orders k ell)
  have h := span_matrix_equations k ell a (archivedLaurentSource k ell) (by
    rw [← ha, ← archivedSource]
    exact eq)
  refine ⟨columnWeights a, ?_⟩
  intro i hm
  have hr : i < 41 := by simpa [SchwarzschildMatrix.rows] using hm
  rw [h i hm, sourceEntry_correct k ell i hr]

theorem matrix_equations_from_homogeneous_span (k ell : ℂ) (a : Row (ℕ → ℂ))
    (eq : rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k
      (laurentSpan 12 a.1, laurentSpan 10 a.2.1, laurentSpan 8 a.2.2) = 0) :
    ∀ i ∈ SchwarzschildMatrix.rows, SchwarzschildMatrix.matrixApply k ell (columnWeights a) i = 0 := by
  intro i hm
  have he := span_matrix_equations k ell a 0 (by rw [mapRow_zero]; exact eq) i hm
  simpa only [rowComponent_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he

private theorem gamma_im_zero (n : ℕ) : (SchwarzschildMatrix.gamma (((n:ℤ):ℂ))).im = 0 := by
  have h : Complex.ofRealHom (SchwarzschildMatrix.gamma (((n:ℤ):ℝ))) =
      SchwarzschildMatrix.gamma (((n:ℤ):ℂ)) := by
    simp only [SchwarzschildMatrix.gamma, map_div₀, map_mul, map_sub, map_add, map_one,
      map_ofNat, map_intCast]
  rw [← h]
  rfl

/-- Exclusion for the exact archived pole-subtracted odd source over C(r), for all
    physical labels and all nonzero purely imaginary frequencies. -/
theorem archived_rational_row_no_solution (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (hi : k.re = 0) :
    let ell : ℂ := ((n:ℤ):ℂ)
    ¬ ∃ u : Row ℂᵣ, rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k u = archivedSource k ell := by
  dsimp only
  have hgamma : k ≠ SchwarzschildMatrix.gamma (((n:ℤ):ℂ)) := by
    intro he
    apply hk
    apply Complex.ext
    · simpa using hi
    · rw [he, gamma_im_zero, Complex.zero_im]
  rintro ⟨u, eu⟩
  exact SchwarzschildMatrix.no_solution n hn k hk hgamma
    (matrix_equations_from_rational_solution k _ hk hi u eu)

#print axioms matrix_equations_from_rational_solution
#print axioms matrix_equations_from_homogeneous_span
#print axioms archived_rational_row_no_solution

end

end SchwarzschildLaurent
