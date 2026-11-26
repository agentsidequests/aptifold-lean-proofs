import MixturePolynomials
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.LinearCombination

/-! Check an integer polynomial identity by exact evaluation at a power of two.
The coefficient bound prevents carrying between digits. The separate degree
bounds prevent two radius/frequency/angular monomials sharing an index. -/
namespace SchwarzschildMixtures
open Polynomial

namespace Term

theorem index_multiply (a b : Term) : (a.multiply b).index = a.index + b.index := by
  unfold index multiply
  dsimp
  omega

end Term

namespace Poly

noncomputable section

def packedPolynomial : Poly → ℤ[X]
  | [] => 0
  | t::ts => monomial t.index t.coefficient + packedPolynomial ts

theorem packed_append (p q : Poly) :
    packedPolynomial (p++q) = packedPolynomial p + packedPolynomial q := by
  induction p with
  | nil => simp [packedPolynomial]
  | cons a p ih => simp [packedPolynomial, ih, add_assoc]

theorem coefficient_bound (p : Poly) (i : ℕ) : ((packedPolynomial p).coeff i).natAbs ≤ mass p := by
  induction p with
  | nil => simp [packedPolynomial, mass]
  | cons a p ih =>
    simp only [packedPolynomial, mass, List.map_cons, List.sum_cons, coeff_add] at ih ⊢
    apply (Int.natAbs_add_le _ _).trans
    apply Nat.add_le_add _ ih
    simp only [coeff_monomial]
    split <;> simp

private def decodedTerm (k ell : ℂ) (i : ℕ) (c : ℤ) : ℂ[X] :=
  termValue k ell ⟨i/1024, (i/64)%16, i%64, c⟩

private theorem decodedTerm_zero (k ell : ℂ) (i : ℕ) : decodedTerm k ell i 0 = 0 := by
  simp [decodedTerm, termValue]

private theorem decodedTerm_add (k ell : ℂ) (i : ℕ) (a b : ℤ) :
    decodedTerm k ell i (a+b) = decodedTerm k ell i a + decodedTerm k ell i b := by
  simp [decodedTerm, termValue, add_mul]

/-- Recover the value in the radius polynomials at arbitrary complex parameters. -/
theorem decode_coefficients (k ell : ℂ) (p : Poly)
    (h : ∀ t ∈ p, t.frequency < 16 ∧ t.angular < 64) :
    (packedPolynomial p).sum (decodedTerm k ell) = value k ell p := by
  induction p with
  | nil => simp [packedPolynomial, value]
  | cons a p ih =>
    have ha := h a (List.mem_cons_self ..)
    have hp : ∀ t ∈ p, t.frequency < 16 ∧ t.angular < 64 :=
      fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hr : a.index/1024 = a.radial := by unfold Term.index; omega
    have hk : (a.index/64)%16 = a.frequency := by unfold Term.index; omega
    have hl : a.index%64 = a.angular := by unfold Term.index; omega
    rw [packedPolynomial, sum_add_index _ _ _ (decodedTerm_zero k ell) (decodedTerm_add k ell),
      sum_monomial_index _ _ (decodedTerm_zero k ell _), ih hp]
    simp only [decodedTerm, hr, hk, hl, value]

end

/-- A nonzero integer polynomial with every coefficient smaller in absolute
value than the base cannot vanish at that base. -/
theorem polynomial_eq_zero_of_packed_zero (p : ℤ[X]) (base : ℕ) (hb : 0 < base)
    (hc : ∀ i, (p.coeff i).natAbs < base) (he : p.eval (base : ℤ) = 0) : p = 0 := by
  suffices ∀ bound : ℕ, ∀ (p : ℤ[X]), p.natDegree ≤ bound →
      (∀ i, (p.coeff i).natAbs < base) → p.eval (base : ℤ) = 0 → p = 0 from
    this p.natDegree p le_rfl hc he
  intro bound
  induction bound with
  | zero =>
    intro p h _ he
    rw [eq_C_of_natDegree_le_zero h] at he ⊢
    simpa using he
  | succ bound ih =>
    intro p h hc he
    have decomp := congrArg (Polynomial.eval (base : ℤ)) (X_mul_divX_add p)
    simp only [eval_add, eval_mul, eval_X, eval_C, he] at decomp
    have hd : (base : ℤ) ∣ p.coeff 0 := by
      refine ⟨-p.divX.eval (base : ℤ), ?_⟩
      linear_combination decomp
    have hzero : p.coeff 0 = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hc 0)
    rw [hzero, add_zero] at decomp
    have hb' : (base : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    have he' := (mul_eq_zero.mp decomp).resolve_left hb'
    have hd' : p.divX.natDegree ≤ bound := by
      rw [natDegree_divX_eq_natDegree_tsub_one]
      omega
    have hz := ih p.divX hd' (fun i => by simpa only [coeff_divX] using hc (i+1)) he'
    rw [← X_mul_divX_add p, hz, hzero]
    simp

theorem powerOfBase_eq (bits index : ℕ) :
    powerOfBase bits index = (↑(2^bits : ℕ) : ℤ)^index := by
  simp [powerOfBase, Nat.shiftLeft_eq, pow_mul]

private theorem lowIndex_le (p : Poly) (t : Term) (ht : t ∈ p) : lowIndex p ≤ t.index := by
  induction p with
  | nil => simp at ht
  | cons a p ih =>
    cases p with
    | nil => simp [lowIndex, List.mem_singleton.mp ht]
    | cons b p =>
      rcases List.mem_cons.mp ht with he | ht
      · subst t
        exact Nat.min_le_left _ _
      · exact (Nat.min_le_right _ _).trans (ih ht)

private theorem encode_relative (bits low : ℕ) (p : Poly) (h : ∀ t ∈ p, low ≤ t.index) :
    powerOfBase bits low * encodeRelative bits low p =
      (packedPolynomial p).eval (↑(2^bits : ℕ) : ℤ) := by
  induction p with
  | nil => simp [encodeRelative, packedPolynomial]
  | cons a p ih =>
    have ha := h a (List.mem_cons_self ..)
    have hp : ∀ t ∈ p, low ≤ t.index := fun t ht => h t (List.mem_cons_of_mem _ ht)
    simp only [encodeRelative, packedPolynomial, mul_add, eval_add, eval_monomial, ih hp]
    congr 1
    rw [powerOfBase_eq, powerOfBase_eq]
    rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le ha]

theorem encodeBlock_correct (bits : ℕ) (p : Poly) :
    encodeBlock bits p = (packedPolynomial p).eval (↑(2^bits : ℕ) : ℤ) :=
  encode_relative bits (lowIndex p) p (lowIndex_le p)

theorem value_zero_of_encoding_zero (bits : ℕ) (p : Poly)
    (h : ∀ t ∈ p, t.frequency < 16 ∧ t.angular < 64)
    (bound : mass p < 2^bits) (packed : (packedPolynomial p).eval (↑(2^bits : ℕ) : ℤ) = 0)
    (k ell : ℂ) : value k ell p = 0 := by
  have hz := polynomial_eq_zero_of_packed_zero _ _ (Nat.two_pow_pos _)
    (fun i => (coefficient_bound p i).trans_lt bound) packed
  rw [← decode_coefficients k ell p h, hz]
  simp

end Poly

namespace CoefficientBand

private theorem base_pos : 0 < base := Nat.two_pow_pos _

private theorem evaluate_digits (r k w count i p n : ℕ)
    (hp : p < base^count) (hn : n < base^count) :
    (Poly.packedPolynomial (digits r k w count i p n)).eval (base : ℤ) =
      (w : ℤ) * ((p : ℤ) - (n : ℤ)) * (base : ℤ)^(1024*r+64*k+i) := by
  induction count generalizing i p n with
  | zero =>
    have hp' : p = 0 := by simpa using hp
    have hn' : n = 0 := by simpa using hn
    simp [digits, Poly.packedPolynomial, hp', hn']
  | succ count ih =>
    have hpd : p/base < base^count :=
      (Nat.div_lt_iff_lt_mul base_pos).mpr (by simpa only [pow_succ] using hp)
    have hnd : n/base < base^count :=
      (Nat.div_lt_iff_lt_mul base_pos).mpr (by simpa only [pow_succ] using hn)
    have p_split : (base : ℤ) * ↑(p/base) + ↑(p%base) = (p : ℤ) := by
      exact_mod_cast Nat.div_add_mod p base
    have n_split : (base : ℤ) * ↑(n/base) + ↑(n%base) = (n : ℤ) := by
      exact_mod_cast Nat.div_add_mod n base
    simp only [digits, Poly.packedPolynomial, eval_add, eval_monomial, Term.index, ih (i+1) _ _ hpd hnd]
    rw [← Nat.add_assoc, pow_succ]
    linear_combination
      (w : ℤ) * (base : ℤ)^(1024*r+64*k+i) * (p_split - n_split)

theorem encode_correct (g : CoefficientBand) :
    g.encode = (Poly.packedPolynomial g.terms).eval (base : ℤ) := by
  rw [encode, Poly.powerOfBase_eq, terms]
  symm
  exact evaluate_digits _ _ _ _ 0 _ _
    (Nat.mod_lt _ (pow_pos base_pos _)) (Nat.mod_lt _ (pow_pos base_pos _))

end CoefficientBand
end SchwarzschildMixtures
