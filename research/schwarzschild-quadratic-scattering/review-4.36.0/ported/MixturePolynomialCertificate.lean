import MixtureIntegerEncoding

/-! Exact addition, multiplication and radius differentiation on coefficient
expressions. Packed evaluation keeps products of large input rows compact. -/
namespace SchwarzschildMixtures
open Polynomial

namespace Poly

def rawMultiply (p q : Poly) : Poly := p.flatMap fun t => q.map t.multiply

theorem mass_append (p q : Poly) : mass (p ++ q) = mass p + mass q := by
  simp [mass, List.sum_append]

theorem mass_neg (p : Poly) : mass (neg p) = mass p := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa [mass, neg] using congrArg (fun x => a.coefficient.natAbs + x) ih

private theorem mass_shift (t : Term) (p : Poly) :
    mass (p.map t.multiply) = t.coefficient.natAbs * mass p := by
  induction p with
  | nil => simp [mass]
  | cons a p ih =>
    simp [mass, Term.multiply, Int.natAbs_mul, Nat.mul_add] at ih ⊢
    rw [ih]

theorem mass_rawMultiply (p q : Poly) : mass (rawMultiply p q) = mass p * mass q := by
  induction p with
  | nil => simp [rawMultiply, mass]
  | cons a p ih =>
    change mass (q.map a.multiply ++ rawMultiply p q) =
      (a.coefficient.natAbs + mass p) * mass q
    rw [mass_append, mass_shift, ih, Nat.add_mul]

theorem value_rawMultiply (k ell : ℂ) (p q : Poly) :
    value k ell (rawMultiply p q) = value k ell p * value k ell q := by
  induction p with
  | nil => simp [rawMultiply, value]
  | cons a p ih =>
    change value k ell (q.map a.multiply ++ rawMultiply p q) =
      (termValue k ell a + value k ell p) * value k ell q
    rw [value_append, value_shift, ih, add_mul]

theorem packed_neg (p : Poly) : packedPolynomial (neg p) = -packedPolynomial p := by
  induction p with
  | nil => simp [neg, packedPolynomial]
  | cons a p ih =>
    change monomial a.index (-a.coefficient) + packedPolynomial (neg p) =
      -(monomial a.index a.coefficient + packedPolynomial p)
    rw [ih, map_neg, neg_add]

private theorem packed_shift (t : Term) (p : Poly) :
    packedPolynomial (p.map t.multiply) = monomial t.index t.coefficient * packedPolynomial p := by
  induction p with
  | nil => simp [packedPolynomial]
  | cons a p ih =>
    simp only [List.map_cons, packedPolynomial, ih, mul_add, monomial_mul_monomial, Term.index_multiply]
    rfl

theorem packed_rawMultiply (p q : Poly) :
    packedPolynomial (rawMultiply p q) = packedPolynomial p * packedPolynomial q := by
  induction p with
  | nil => simp [rawMultiply, packedPolynomial]
  | cons a p ih =>
    change packedPolynomial (q.map a.multiply ++ rawMultiply p q) =
      (monomial a.index a.coefficient + packedPolynomial p) * packedPolynomial q
    rw [packed_append, packed_shift, ih, add_mul]

theorem derivative_append (p q : Poly) : derivative (p++q) = derivative p ++ derivative q := by
  induction p with
  | nil => simp [derivative]
  | cons a p ih =>
    rcases a with ⟨r,k,l,c⟩
    cases r <;> simp [derivative, ih]

end Poly

namespace CoefficientBand

private theorem derivative_digits_zero (k w count i p n : ℕ) :
    Poly.derivative (digits 0 k w count i p n) = [] := by
  induction count generalizing i p n with
  | zero => rfl
  | succ count ih => simp only [digits, Poly.derivative, ih]

private theorem derivative_digits_succ (r k w count i p n : ℕ) :
    Poly.derivative (digits (r+1) k w count i p n) =
      digits r k (w*(r+1)) count i p n := by
  induction count generalizing i p n with
  | zero => rfl
  | succ count ih =>
    simp only [digits, Poly.derivative, ih, Int.natCast_mul]
    congr 2
    ring

theorem derivative_terms (g : CoefficientBand) :
    ((g.derivative.map CoefficientBand.terms).getD []) = Poly.derivative g.terms := by
  rcases g with ⟨r,k,count,p,n,w⟩
  cases r with
  | zero => simp [derivative, terms, derivative_digits_zero]
  | succ r => simp [derivative, terms, derivative_digits_succ]

private theorem atHorizon_digits (r k w count i p n : ℕ) :
    Expr.substituteTwo (digits r k w count i p n) =
      digits 0 k (w*2^r) count i p n := by
  induction count generalizing i p n with
  | zero => rfl
  | succ count ih =>
    simp only [Expr.substituteTwo, digits, List.map_cons, Int.natCast_mul, Int.natCast_pow,
      Nat.cast_ofNat] at ih ⊢
    rw [ih]
    congr 2
    ring

theorem atHorizon_terms (g : CoefficientBand) :
    g.atHorizon.terms = Expr.substituteTwo g.terms :=
  (atHorizon_digits _ _ _ _ _ _ _).symm

end CoefficientBand

namespace Expr

noncomputable section

def value (k ell : ℂ) : Expr → ℂ[X]
  | .coefficients ps => Poly.value k ell ps.flatten
  | .bands rows => Poly.value k ell (rows.map CoefficientBand.terms).flatten
  | .add p q => value k ell p + value k ell q
  | .neg p => -value k ell p
  | .mul p q => value k ell p * value k ell q

theorem value_single (k ell : ℂ) (a : ℤ) (i j s : ℕ) :
    value k ell (single a i j s) = C ((a : ℂ) * k^j * ell^s) * X^i := by
  simpa [single, value] using Poly.value_single k ell a i j s

theorem value_constant (k ell : ℂ) (a : ℤ) : value k ell (constant a) = C (a : ℂ) := by
  simp [constant, value_single]

@[simp] theorem value_frequency (k ell : ℂ) : value k ell frequency = C k := by
  simp [frequency, value_single]

@[simp] theorem value_angular (k ell : ℂ) : value k ell angular = C ell := by
  simp [angular, value_single]

@[simp] theorem value_add (k ell : ℂ) (p q : Expr) :
    value k ell (.add p q) = value k ell p + value k ell q := rfl

@[simp] theorem value_neg (k ell : ℂ) (p : Expr) :
    value k ell (.neg p) = -value k ell p := rfl

@[simp] theorem value_mul (k ell : ℂ) (p q : Expr) :
    value k ell (.mul p q) = value k ell p * value k ell q := rfl

@[simp] theorem value_sub (k ell : ℂ) (p q : Expr) :
    value k ell (sub p q) = value k ell p - value k ell q := by
  rw [sub, value_add, value_neg, sub_eq_add_neg]

@[simp] theorem value_derivative (k ell : ℂ) (p : Expr) :
    value k ell (derivative p) = (value k ell p).derivative := by
  have flatten_derivative (ps : List Poly) :
      (ps.map Poly.derivative).flatten = Poly.derivative ps.flatten := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [Poly.derivative_append, ih]
  have bands_derivative (gs : List CoefficientBand) :
      ((gs.filterMap CoefficientBand.derivative).map CoefficientBand.terms).flatten =
        Poly.derivative (gs.map CoefficientBand.terms).flatten := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have hg := g.derivative_terms
      cases eq : g.derivative <;>
        simp [eq, Poly.derivative_append, ← hg, ih]
  induction p with
  | coefficients ps => simp [value, derivative, flatten_derivative]
  | bands rows => simp [value, derivative, bands_derivative]
  | add p q ihp ihq => simp [derivative, ihp, ihq]
  | neg p ih => simp [derivative, ih]
  | mul p q ihp ihq => simp [derivative, ihp, ihq, derivative_mul]

@[simp] theorem value_atHorizon (k ell : ℂ) (p : Expr) :
    value k ell (atHorizon p) = C ((value k ell p).eval 2) := by
  have values (p : Poly) :
      Poly.value k ell (substituteTwo p) = C ((Poly.value k ell p).eval 2) := by
    induction p with
    | nil => simp [substituteTwo, Poly.value]
    | cons t p ih =>
      simp only [substituteTwo, List.map_cons, Poly.value, Poly.termValue, Int.cast_mul,
        Int.cast_pow, Int.cast_ofNat, pow_zero, mul_one, eval_add, eval_mul, eval_C,
        eval_pow, eval_X, map_add] at ih ⊢
      rw [ih]
      have hc : (t.coefficient : ℂ) * (2:ℂ)^t.radial * k^t.frequency * ell^t.angular =
          (t.coefficient : ℂ) * k^t.frequency * ell^t.angular * (2:ℂ)^t.radial := by ring
      rw [hc]
  have flat (ps : List Poly) : (ps.map substituteTwo).flatten = substituteTwo ps.flatten := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons, List.flatten_cons, ih]
      simp [substituteTwo, List.map_append]
  induction p with
  | coefficients ps => simp [atHorizon, value, flat, values]
  | bands rows =>
    simp only [atHorizon, value, List.map_map, Function.comp_def, CoefficientBand.atHorizon_terms]
    change Poly.value k ell ((rows.map (substituteTwo ∘ CoefficientBand.terms)).flatten) = _
    rw [← List.map_map, flat, values]
  | add p q hp hq => simp [atHorizon, value, hp, hq]
  | neg p hp => simp [atHorizon, value, hp]
  | mul p q hp hq => simp [atHorizon, value, hp, hq]

private def raw : Expr → Poly
  | .coefficients ps => ps.flatten
  | .bands rows => (rows.map CoefficientBand.terms).flatten
  | .add p q => raw p ++ raw q
  | .neg p => (raw p).neg
  | .mul p q => Poly.rawMultiply (raw p) (raw q)

private theorem raw_value (k ell : ℂ) (p : Expr) : (raw p).value k ell = value k ell p := by
  induction p <;> simp [raw, value, Poly.value_append, Poly.value_rawMultiply, *]

end

private structure Covers (b : Bounds) (p : Poly) : Prop where
  degrees : ∀ t ∈ p, t.frequency ≤ b.frequency ∧ t.angular ≤ b.angular
  mass : p.mass ≤ b.mass

private theorem covers_nil : Covers ⟨0,0,0⟩ [] :=
  ⟨by simp, Nat.le_refl 0⟩

private theorem covers_append {a b : Bounds} {p q : Poly} (ha : Covers a p) (hb : Covers b q) :
    Covers (mergeBounds a b) (p++q) := by
  constructor
  · intro t ht
    rcases List.mem_append.mp ht with hp | hq
    · have h := ha.degrees t hp
      exact ⟨h.1.trans (le_max_left ..), h.2.trans (le_max_left ..)⟩
    · have h := hb.degrees t hq
      exact ⟨h.1.trans (le_max_right ..), h.2.trans (le_max_right ..)⟩
  · rw [Poly.mass_append]
    exact Nat.add_le_add ha.mass hb.mass

private theorem list_covered (p : Poly) : Covers (boundsOfList p) p := by
  induction p with
  | nil => exact covers_nil
  | cons a p ih =>
    have ha : Covers (termBounds a) [a] := by
      constructor
      · intro t ht
        simp [List.mem_singleton.mp ht, termBounds]
      · simp [termBounds, Poly.mass]
    exact covers_append ha ih

private theorem blocks_covered (ps : List Poly) :
    Covers (ps.foldr (mergeBounds ∘ boundsOfList) ⟨0,0,0⟩) ps.flatten := by
  induction ps with
  | nil => exact covers_nil
  | cons p ps ih => exact covers_append (list_covered p) ih

private theorem covered (p : Expr) : Covers (bounds p) (raw p) := by
  induction p with
  | coefficients ps => exact blocks_covered ps
  | bands rows =>
    simpa [bounds, raw, List.foldr_map, Function.comp_def]
      using blocks_covered (rows.map CoefficientBand.terms)
  | add p q ihp ihq => exact covers_append ihp ihq
  | neg p ih =>
    have hm := ih.mass
    constructor
    · intro t ht
      obtain ⟨v, hv, eq⟩ := List.mem_map.mp ht
      cases eq
      exact ih.degrees v hv
    · simpa [bounds, raw, Poly.mass_neg] using hm
  | mul p q ihp ihq =>
    constructor
    · intro t ht
      obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨b, hb, eq⟩ := List.mem_map.mp ht
      cases eq
      exact ⟨Nat.add_le_add (ihp.degrees a ha).1 (ihq.degrees b hb).1,
        Nat.add_le_add (ihp.degrees a ha).2 (ihq.degrees b hb).2⟩
    · rw [raw, Poly.mass_rawMultiply]
      exact Nat.mul_le_mul ihp.mass ihq.mass

private theorem encode_correct (p : Expr) :
    encode p = (Poly.packedPolynomial (raw p)).eval (CoefficientBand.base : ℤ) := by
  have blocks (ps : List Poly) :
      (ps.map (Poly.encodeBlock 112)).sum =
        (Poly.packedPolynomial ps.flatten).eval (CoefficientBand.base : ℤ) := by
    induction ps with
    | nil => simp [Poly.packedPolynomial]
    | cons p ps ih =>
      have hp : Poly.encodeBlock 112 p =
          (Poly.packedPolynomial p).eval (CoefficientBand.base : ℤ) := Poly.encodeBlock_correct _ _
      simp [Poly.packed_append, hp, ih]
  have bandBlocks (gs : List CoefficientBand) :
      (gs.map CoefficientBand.encode).sum =
        (Poly.packedPolynomial (gs.map CoefficientBand.terms).flatten).eval (CoefficientBand.base : ℤ) := by
    induction gs with
    | nil => simp [Poly.packedPolynomial]
    | cons g gs ih => simp [Poly.packed_append, CoefficientBand.encode_correct, ih]
  induction p <;> simp [encode, raw, Poly.packed_append, Poly.packed_neg, Poly.packed_rawMultiply, *]

/-- The computation compares integers. Its implication for the symbolic
polynomials is proved for every complex frequency and angular label. -/
theorem value_eq_of_check (p q : Expr) (check : Check p q) (k ell : ℂ) :
    value k ell p = value k ell q := by
  obtain ⟨kf, lf, mass, eq⟩ := check
  have cov := covered (sub p q)
  have he : encode (sub p q) = 0 := by simp [sub, encode, eq]
  rw [encode_correct] at he
  have hz := Poly.value_zero_of_encoding_zero _ _ (fun t ht =>
    ⟨(cov.degrees t ht).1.trans_lt kf, (cov.degrees t ht).2.trans_lt lf⟩)
    (cov.mass.trans_lt mass) he k ell
  rw [raw_value, value_sub] at hz
  exact sub_eq_zero.mp hz

end Expr
end SchwarzschildMixtures
