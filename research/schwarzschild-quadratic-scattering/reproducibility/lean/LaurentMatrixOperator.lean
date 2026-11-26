import ArchivedRationalSource

/-! Interpret the exact Laurent-list operator that generates the matrix columns. -/
namespace SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

def matrixTermValue (k ell : ℂ) (t : SchwarzschildMatrix.LaurentTerm) : LPoly :=
  AddMonoidAlgebra.single t.radius (SchwarzschildMatrix.evalMonomial k ell (t.frequency, t.angular, t.coefficient))

def matrixListValue (k ell : ℂ) : SchwarzschildMatrix.Laurent → LPoly
  | [] => 0
  | t :: ts => matrixTermValue k ell t + matrixListValue k ell ts

def matrixListRat (k ell : ℂ) (p : SchwarzschildMatrix.Laurent) : ℂᵣ :=
  laurentToRat (matrixListValue k ell p)

theorem matrixListRat_nil (k ell : ℂ) : matrixListRat k ell [] = 0 := map_zero laurentToRat

private theorem matrixListRat_cons (k ell : ℂ) (t : SchwarzschildMatrix.LaurentTerm)
    (p : SchwarzschildMatrix.Laurent) :
    matrixListRat k ell (t :: p) =
      Cᵣ (SchwarzschildMatrix.evalMonomial k ell (t.frequency, t.angular, t.coefficient)) * R^t.radius +
        matrixListRat k ell p := by
  simp only [matrixListRat, matrixListValue, map_add, matrixTermValue, laurentToRat_single]

private theorem matrixListValue_append (k ell : ℂ) (p q : SchwarzschildMatrix.Laurent) :
    matrixListValue k ell (p ++ q) = matrixListValue k ell p + matrixListValue k ell q := by
  induction p with
  | nil => simp [matrixListValue]
  | cons t p ih => simp [matrixListValue, ih, add_assoc]

private theorem matrixListRat_append (k ell : ℂ) (p q : SchwarzschildMatrix.Laurent) :
    matrixListRat k ell (p ++ q) = matrixListRat k ell p + matrixListRat k ell q := by
  simp only [matrixListRat, matrixListValue_append, map_add]

private theorem termTimes (k ell : ℂ) (a b : SchwarzschildMatrix.LaurentTerm) :
    matrixTermValue k ell ⟨a.radius+b.radius, a.frequency+b.frequency, a.angular+b.angular,
        a.coefficient * b.coefficient⟩ =
      matrixTermValue k ell a * matrixTermValue k ell b := by
  simp only [matrixTermValue, AddMonoidAlgebra.single_mul_single, SchwarzschildMatrix.evalMonomial,
    Int.cast_mul, pow_add]
  congr 1
  ring

private theorem matrixListValue_multiply (k ell : ℂ) (p q : SchwarzschildMatrix.Laurent) :
    matrixListValue k ell (SchwarzschildMatrix.multiplyLaurent p q) =
      matrixListValue k ell p * matrixListValue k ell q := by
  have distribute (a : SchwarzschildMatrix.LaurentTerm) (ts : SchwarzschildMatrix.Laurent) :
      matrixListValue k ell (ts.map fun b => ⟨a.radius+b.radius, a.frequency+b.frequency,
        a.angular+b.angular, a.coefficient*b.coefficient⟩) =
        matrixTermValue k ell a * matrixListValue k ell ts := by
    induction ts with
    | nil => simp [matrixListValue]
    | cons b ts ih =>
      simp only [List.map_cons, matrixListValue, termTimes, ih, mul_add]
  induction p with
  | nil => simp [SchwarzschildMatrix.multiplyLaurent, matrixListValue]
  | cons t p ih =>
    rw [show SchwarzschildMatrix.multiplyLaurent (t::p) q =
      (q.map fun b => ⟨t.radius+b.radius, t.frequency+b.frequency, t.angular+b.angular,
        t.coefficient*b.coefficient⟩) ++ SchwarzschildMatrix.multiplyLaurent p q from rfl]
    rw [matrixListValue_append, distribute, ih, matrixListValue, add_mul]

private theorem matrixListRat_multiply (k ell : ℂ) (p q : SchwarzschildMatrix.Laurent) :
    matrixListRat k ell (SchwarzschildMatrix.multiplyLaurent p q) =
      matrixListRat k ell p * matrixListRat k ell q := by
  simp only [matrixListRat, matrixListValue_multiply, map_mul]

private theorem matrixListRat_scale (k ell : ℂ) (n : ℤ) (p : SchwarzschildMatrix.Laurent) :
    matrixListRat k ell (SchwarzschildMatrix.scaleLaurent n p) = (n:ℂᵣ) * matrixListRat k ell p := by
  induction p with
  | nil => simp [SchwarzschildMatrix.scaleLaurent, matrixListRat_nil]
  | cons t p ih =>
    rw [show SchwarzschildMatrix.scaleLaurent n (t::p) =
      {t with coefficient := n*t.coefficient} :: SchwarzschildMatrix.scaleLaurent n p from rfl]
    simp only [matrixListRat_cons, ih, SchwarzschildMatrix.evalMonomial, Int.cast_mul,
      map_mul, map_intCast]
    ring

private theorem matrixListRat_shift (k ell : ℂ) (n : ℤ) (p : SchwarzschildMatrix.Laurent) :
    matrixListRat k ell (SchwarzschildMatrix.shiftRadius n p) = R^n * matrixListRat k ell p := by
  induction p with
  | nil => simp [SchwarzschildMatrix.shiftRadius, matrixListRat_nil]
  | cons t p ih =>
    rw [show SchwarzschildMatrix.shiftRadius n (t::p) =
      {t with radius := t.radius+n} :: SchwarzschildMatrix.shiftRadius n p from rfl]
    simp only [matrixListRat_cons, ih, zpow_add₀ (a := R) RatFunc.X_ne_zero]
    ring

private theorem matrixListRat_f (k ell : ℂ) : matrixListRat k ell SchwarzschildMatrix.f = radialFactor := by
  simp only [SchwarzschildMatrix.f, matrixListRat_cons, matrixListRat_nil,
    SchwarzschildMatrix.evalMonomial, pow_zero, mul_one, add_zero, zpow_zero, zpow_neg_one,
    Int.cast_one, Int.cast_neg, Int.cast_ofNat, map_one, map_neg, map_ofNat, radialFactor]
  field_simp [RatFunc.X_ne_zero]
  ring

private theorem matrixListRat_potential (k ell : ℂ) (n : ℤ) :
    matrixListRat k ell (SchwarzschildMatrix.potential n) = oddPotential ((n:ℂ)*ell*((n:ℂ)*ell+1)) := by
  simp only [SchwarzschildMatrix.potential, matrixListRat_multiply, matrixListRat_f,
    matrixListRat_cons, matrixListRat_nil, SchwarzschildMatrix.evalMonomial, pow_zero, pow_one,
    mul_one, add_zero, zpow_neg, zpow_ofNat, map_intCast, map_mul, map_add, map_one, Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat, map_pow, oddPotential]
  congr 1
  field_simp [RatFunc.X_ne_zero]
  ring

private theorem matrixListRat_radialDerivative (k ell : ℂ) (p : SchwarzschildMatrix.Laurent) :
    matrixListRat k ell (SchwarzschildMatrix.radialDerivative p) = radialFactor * δ (matrixListRat k ell p) := by
  have delta (q : SchwarzschildMatrix.Laurent) :
      matrixListRat k ell (q.filterMap fun t => if t.radius == 0 then none else
        some {t with radius := t.radius-1, coefficient := t.radius*t.coefficient}) =
        δ (matrixListRat k ell q) := by
    induction q with
    | nil => simp only [List.filterMap_nil, matrixListRat_nil, rationalDerivative_zero]
    | cons t q ih =>
      rw [List.filterMap_cons]
      by_cases hz : t.radius = 0
      · simp only [hz, beq_self_eq_true, if_true, matrixListRat_cons, zpow_zero, mul_one,
          rationalDerivative_add, rationalDerivative_constant, zero_add, ih]
      · simp only [beq_iff_eq] at ih
        simp only [beq_iff_eq, if_neg hz, matrixListRat_cons, rationalDerivative_add,
          rationalDerivative_mul, rationalDerivative_constant, zero_mul, zero_add,
          rationalDerivative_radius_zpow, ih]
        simp only [SchwarzschildMatrix.evalMonomial, Int.cast_mul, map_mul, map_intCast]
        ring
  rw [SchwarzschildMatrix.radialDerivative, matrixListRat_multiply, matrixListRat_f, delta]

private theorem matrixListRat_a (k ell : ℂ) :
    matrixListRat k ell SchwarzschildMatrix.a =
      R^2*(Cᵣ (k^2)+oddPotential (ell*(ell+1))) := by
  simp only [SchwarzschildMatrix.a, matrixListRat_append, matrixListRat_cons, matrixListRat_nil,
    matrixListRat_shift, matrixListRat_potential, SchwarzschildMatrix.evalMonomial, Int.cast_one,
    pow_zero, mul_one, one_mul, add_zero, zpow_ofNat, mul_add]
  ring

private theorem matrixListRat_b (k ell : ℂ) :
    matrixListRat k ell SchwarzschildMatrix.b = 2*radialFactor/R := by
  simp only [SchwarzschildMatrix.b, matrixListRat_scale, matrixListRat_shift, matrixListRat_f,
    zpow_neg_one, Int.cast_ofNat, div_eq_mul_inv]
  ring

private theorem matrixListRat_c (k ell : ℂ) :
    matrixListRat k ell SchwarzschildMatrix.c = 1/R^2 := by
  simp [SchwarzschildMatrix.c, matrixListRat_cons, matrixListRat_nil,
    SchwarzschildMatrix.evalMonomial, zpow_neg, zpow_ofNat]

private theorem matrixListRat_daughterHead (k ell : ℂ) :
    matrixListRat k ell [⟨0, 2, 0, 4⟩] = Cᵣ (4*k^2) := by
  simp [matrixListRat_cons, matrixListRat_nil, SchwarzschildMatrix.evalMonomial]

theorem matrix_derivative_correct (k ell : ℂ) (u : SchwarzschildMatrix.LaurentRow) :
    mapRow (matrixListRat k ell) (SchwarzschildMatrix.derivative u) =
      rationalStep (ell*(ell+1)) k (mapRow (matrixListRat k ell) u) := by
  rcases u with ⟨p,q,s⟩
  rw [rationalStep_physical]
  simp only [mapRow, SchwarzschildMatrix.derivative, plus, jet, scale, rationalRowDerivative,
    matrixListRat_append, matrixListRat_multiply, matrixListRat_scale, matrixListRat_radialDerivative,
    matrixListRat_a, matrixListRat_b, matrixListRat_c, Int.cast_ofNat]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> ring

theorem matrix_operator_correct (k ell : ℂ) (u : SchwarzschildMatrix.LaurentRow) :
    mapRow (matrixListRat k ell) (SchwarzschildMatrix.operator u) =
      rationalOperator (ell*(ell+1)) ((2*ell)*(2*ell+1)) k (mapRow (matrixListRat k ell) u) := by
  rw [rationalOperator, ← matrix_derivative_correct, ← matrix_derivative_correct]
  apply Prod.ext
  · simp only [SchwarzschildMatrix.operator, mapRow, minus, scale, matrixListRat_append,
      matrixListRat_scale, matrixListRat_multiply, matrixListRat_daughterHead, matrixListRat_potential,
      Int.cast_ofNat, Int.cast_neg, Int.cast_one,
      neg_mul, one_mul, sub_eq_add_neg]
  · apply Prod.ext <;> simp only [SchwarzschildMatrix.operator, mapRow, minus, scale, matrixListRat_append,
      matrixListRat_scale, matrixListRat_multiply, matrixListRat_daughterHead, matrixListRat_potential,
      Int.cast_ofNat, Int.cast_neg, Int.cast_one,
      neg_mul, one_mul, sub_eq_add_neg]

#print axioms matrix_derivative_correct
#print axioms matrix_operator_correct

end

end SchwarzschildLaurent
