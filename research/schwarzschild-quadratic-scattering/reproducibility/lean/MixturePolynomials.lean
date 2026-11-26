import MixtureCoefficientData
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! Interpret the exact input coefficients as complex radial polynomials. -/
namespace SchwarzschildMixtures

open Polynomial

namespace Poly

noncomputable section

def termValue (k ell : ℂ) (t : Term) : ℂ[X] :=
  C ((t.coefficient : ℂ) * k^t.frequency * ell^t.angular) * X^t.radial

def value (k ell : ℂ) : Poly → ℂ[X]
  | [] => 0
  | t::p => termValue k ell t + value k ell p

theorem value_single (k ell : ℂ) (a : ℤ) (i j s : ℕ) :
    value k ell (single a i j s) = C ((a : ℂ) * k^j * ell^s) * X^i := by
  simp [single, value, termValue]

theorem value_append (k ell : ℂ) (p q : Poly) :
    value k ell (p ++ q) = value k ell p + value k ell q := by
  induction p with
  | nil => simp [value]
  | cons a p ih => simp [value, ih, add_assoc]

@[simp] theorem value_neg (k ell : ℂ) (p : Poly) :
    value k ell (neg p) = -value k ell p := by
  induction p with
  | nil => simp [neg, value]
  | cons a p ih =>
    change termValue k ell {a with coefficient := -a.coefficient} + value k ell (neg p) =
      -(termValue k ell a + value k ell p)
    rw [ih]
    simp only [termValue, Int.cast_neg, neg_mul, map_neg, neg_add]

private theorem termValue_multiply (k ell : ℂ) (a b : Term) :
    termValue k ell (a.multiply b) = termValue k ell a * termValue k ell b := by
  simp only [termValue, Term.multiply, Int.cast_mul, pow_add, map_mul]
  ring

theorem value_shift (k ell : ℂ) (a : Term) (p : Poly) :
    value k ell (p.map a.multiply) = termValue k ell a * value k ell p := by
  induction p with
  | nil => simp [value]
  | cons b p ih => simp [value, termValue_multiply, ih, mul_add]

@[simp] theorem value_derivative (k ell : ℂ) (p : Poly) :
    value k ell (derivative p) = (value k ell p).derivative := by
  induction p with
  | nil => simp [derivative, value]
  | cons t p ih =>
    rcases t with ⟨r,j,s,a⟩
    cases r with
    | zero =>
      simp only [derivative, value, termValue, ih, derivative_add, pow_zero, mul_one,
        derivative_C, zero_add]
    | succ r =>
      simp only [derivative, value, termValue, ih, derivative_add, derivative_C_mul_X_pow,
        Nat.succ_sub_one, Int.cast_mul, Int.cast_natCast]
      have h : (a : ℂ) * (↑(r + 1 : ℕ) : ℂ) * k^j * ell^s =
          (a : ℂ) * k^j * ell^s * (↑(r+1 : ℕ) : ℂ) := by ring
      rw [h]

end
end Poly
end SchwarzschildMixtures
