import LaurentBounds
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
Algebraic bridges for the Laurent reduction. The derivative is formal, so the
argument concerns rational identities over the complex numbers.
-/

namespace SchwarzschildLaurent

open Polynomial
open scoped BigOperators

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

/-- The derivative of a complex rational function. -/
noncomputable def rationalDerivative (u : ℂᵣ) : ℂᵣ :=
  ι (u.num.derivative * u.denom - u.num * u.denom.derivative) / (ι u.denom) ^ 2

theorem rationalDerivative_fraction (p q : ℂ[X]) (hq : q ≠ 0) :
    rationalDerivative (ι p / ι q) = ι (p.derivative*q - p*q.derivative) / (ι q)^2 := by
  let u : ℂᵣ := ι p / ι q
  have h : u.num * q = p * u.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).2 rfl
  have hd := congrArg Polynomial.derivative h
  simp only [Polynomial.derivative_mul] at hd
  change ι (u.num.derivative*u.denom - u.num*u.denom.derivative) / (ι u.denom)^2 = _
  apply (div_eq_div_iff (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero u.denom_ne_zero))
    (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hq))).2
  simp_rw [← map_pow, ← map_mul]
  apply congrArg ι
  linear_combination (q*u.denom) * hd - (u.denom.derivative*q + q.derivative*u.denom) * h

noncomputable def localCoordinate (a : ℂ) : ℂ[X] := X - C a

theorem localCoordinate_ne_zero (a : ℂ) : localCoordinate a ≠ 0 := X_sub_C_ne_zero a

/-- The Euler derivative with respect to t = r - a. -/
noncomputable def euler (a : ℂ) (u : ℂᵣ) : ℂᵣ :=
  ι (localCoordinate a) * rationalDerivative u

/-- Numerator of the Euler derivative after extracting the factor t^(-m). -/
noncomputable def eulerNumerator (a : ℂ) (m : ℕ) (p q : ℂ[X]) : ℂ[X] :=
  localCoordinate a * (p.derivative*q - p*q.derivative) - C (m : ℂ) * p * q

private theorem localCoordinate_mul_derivative_pow (a : ℂ) (m : ℕ) :
    localCoordinate a * (localCoordinate a ^ m).derivative =
      C (m : ℂ) * localCoordinate a ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    have h : (localCoordinate a).derivative = 1 := by simp [localCoordinate]
    rw [Polynomial.derivative_pow, h, mul_one, pow_succ]
    simp only [Nat.succ_sub_one]
    ring

theorem euler_fraction (a : ℂ) (m : ℕ) (p q : ℂ[X]) (hq : q ≠ 0) :
    euler a (ι p / ι (localCoordinate a ^ m * q)) =
      ι (eulerNumerator a m p q) / ι (localCoordinate a ^ m * q ^ 2) := by
  have ht := localCoordinate_ne_zero a
  have hh := localCoordinate_mul_derivative_pow a m
  have heq : localCoordinate a *
      (p.derivative * (localCoordinate a ^ m * q) -
        p * (localCoordinate a ^ m * q).derivative) =
      localCoordinate a ^ m * eulerNumerator a m p q := by
    rw [Polynomial.derivative_mul, eulerNumerator]
    linear_combination (-p*q)*hh
  rw [euler, rationalDerivative_fraction p _ (mul_ne_zero (pow_ne_zero _ ht) hq),
      ← mul_div_assoc, ← map_mul, heq]
  simp only [map_mul, map_pow]
  field_simp [RatFunc.algebraMap_ne_zero ht, RatFunc.algebraMap_ne_zero hq]

theorem euler_twice_fraction (a : ℂ) (m : ℕ) (p q : ℂ[X]) (hq : q ≠ 0) :
    euler a (euler a (ι p / ι (localCoordinate a ^ m * q))) =
      ι (eulerNumerator a m (eulerNumerator a m p q) (q^2)) /
        ι (localCoordinate a ^ m * (q^2)^2) := by
  rw [euler_fraction a m p q hq,
      euler_fraction a m (eulerNumerator a m p q) (q^2) (pow_ne_zero 2 hq)]

/-- The first regular coefficient of the normalized Euler numerator. -/
theorem eulerNumerator_eval (a : ℂ) (m : ℕ) (p q : ℂ[X]) :
    (eulerNumerator a m p q).eval a = -(m : ℂ) * p.eval a * q.eval a := by
  simp [eulerNumerator, localCoordinate, neg_mul]

/-- The second normalized Euler derivative contributes the squared pole order. -/
theorem eulerNumerator_twice_eval (a : ℂ) (m : ℕ) (p q : ℂ[X]) :
    (eulerNumerator a m (eulerNumerator a m p q) (q ^ 2)).eval a =
      (m : ℂ)^2 * p.eval a * (q.eval a)^3 := by
  simp only [eulerNumerator_eval, eval_pow]
  ring

/-- A normalized denominator with no nonzero roots is a power of r. -/
theorem denominator_power (u : ℂᵣ)
    (h : ∀ a : ℂ, a ≠ 0 → u.denom.eval a ≠ 0) :
    u.denom = X ^ u.denom.natDegree := by
  have hs : u.denom.Splits := IsAlgClosed.splits _
  have roots₀ : ∀ a ∈ u.denom.roots, a = 0 := by
    intro a ha
    by_contra na
    exact h a na ((mem_roots u.denom_ne_zero).mp ha)
  have hr := Multiset.eq_replicate_card.mpr roots₀
  calc
    u.denom = (u.denom.roots.map fun a => X - C a).prod :=
      hs.eq_prod_roots_of_monic u.monic_denom
    _ = X ^ u.denom.natDegree := by
      rw [hr, Multiset.map_replicate, Multiset.prod_replicate, ← hs.natDegree_eq_card_roots]
      simp

/-- Shift origin pole order at most seven into a polynomial numerator. -/
theorem bounded_laurent_numerator (u : ℂᵣ) (d : ℕ)
    (hfinite : ∀ a : ℂ, a ≠ 0 → u.denom.eval a ≠ 0)
    (horigin : u.denom.natDegree ≤ 7)
    (hinfty : u.num.natDegree ≤ u.denom.natDegree + d) :
    ∃ p : ℂ[X], p.natDegree ≤ 7+d ∧ u = ι p / (RatFunc.X : ℂᵣ)^7 := by
  let m := u.denom.natDegree
  have hp : u.denom = X ^ m := denominator_power u hfinite
  refine ⟨X^(7-m)*u.num, ?_, ?_⟩
  · have h : (X^(7-m)*u.num).natDegree ≤ (X^(7-m) : ℂ[X]).natDegree + u.num.natDegree :=
      Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_X_pow] at h
    dsimp [m] at *
    omega
  · have heq : 7 = (7-m)+m := by dsimp [m]; omega
    conv_lhs => rw [← RatFunc.num_div_denom u]
    simp only [hp, map_mul, map_pow, RatFunc.algebraMap_X]
    conv_rhs => rw [heq, pow_add]
    field_simp [RatFunc.X_ne_zero]
    simp

/-- The component lies in the Laurent span from r⁻⁷ through rᵈ. -/
theorem bounded_laurent_expansion (u : ℂᵣ) (d : ℕ)
    (hfinite : ∀ a : ℂ, a ≠ 0 → u.denom.eval a ≠ 0)
    (horigin : u.denom.natDegree ≤ 7)
    (hinfty : u.num.natDegree ≤ u.denom.natDegree + d) :
    ∃ coeff : ℕ → ℂ, u = ∑ i ∈ Finset.range (d+8),
      RatFunc.C (coeff i) * (RatFunc.X : ℂᵣ) ^ ((i : ℤ) - 7) := by
  obtain ⟨p, hdeg, hu⟩ := bounded_laurent_numerator u d hfinite horigin hinfty
  refine ⟨p.coeff, ?_⟩
  have hs := p.as_sum_range_C_mul_X_pow' (n := d+8) (by omega)
  rw [hu]
  conv_lhs => rw [hs]
  simp only [map_sum, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ RatFunc.X_ne_zero, zpow_natCast]
  rw [show ((7 : ℤ)) = ((7 : ℕ) : ℤ) from rfl, zpow_natCast, mul_div_assoc]

#print axioms rationalDerivative_fraction
#print axioms euler_twice_fraction
#print axioms bounded_laurent_expansion

end SchwarzschildLaurent
