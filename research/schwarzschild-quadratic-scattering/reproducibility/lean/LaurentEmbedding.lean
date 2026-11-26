import RationalSourceReduction
import Mathlib.Algebra.Polynomial.Laurent

/-! Faithful evaluation of Laurent polynomials in the rational function field. -/
namespace SchwarzschildLaurent

noncomputable section

open Polynomial

abbrev LPoly := LaurentPolynomial ℂ

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

def laurentToRat : LPoly →+* ℂᵣ :=
  LaurentPolynomial.eval₂ Cᵣ (Units.mk0 R RatFunc.X_ne_zero)

@[simp] theorem laurentToRat_single (j : ℤ) (a : ℂ) :
    laurentToRat (AddMonoidAlgebra.single j a) = Cᵣ a * R^j := by
  rw [laurentToRat, LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem laurentToRat_polynomial (p : ℂ[X]) : laurentToRat (Polynomial.toLaurent p) = ι p := by
  rw [laurentToRat, LaurentPolynomial.eval₂_toLaurent]
  change p.eval₂ Cᵣ R = ι p
  rw [← RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_X, ← Polynomial.aeval_def]
  change Polynomial.aeval ((IsScalarTower.toAlgHom ℂ ℂ[X] ℂᵣ) X) p = ι p
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply]
  rfl

theorem laurentToRat_injective : Function.Injective laurentToRat := by
  intro a b hab
  apply sub_eq_zero.mp
  let u := a-b
  have hu : laurentToRat u = 0 := by simp [u, hab]
  obtain ⟨m, p, hp⟩ := LaurentPolynomial.exists_T_pow u
  have hz : ι p = 0 := by rw [← laurentToRat_polynomial, hp, map_mul, hu, zero_mul]
  have pzero : p = 0 := (RatFunc.algebraMap_injective ℂ).eq_iff.mp (by simpa using hz)
  have he : u * LaurentPolynomial.T (m : ℤ) = 0 := by rw [← hp, pzero, map_zero]
  have hm := congrArg (fun v => v * LaurentPolynomial.T (-(m : ℤ))) he
  simpa only [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
    mul_one, zero_mul] using hm

theorem rationalDerivative_radius_zpow (j : ℤ) : δ (R^j) = (j : ℂᵣ)*R^(j-1) := by
  have pos (n : ℕ) : R * δ (R^n) = (n : ℂᵣ) * R^n := by
    cases n with
    | zero => simp
    | succ n =>
      rw [rationalDerivative_pow, rationalDerivative_radius, mul_one, Nat.succ_sub_one, pow_succ]
      ring
  have inv {u a : ℂᵣ} (hu : u ≠ 0) (h : R*δ u = a*u) :
      R*δ (u⁻¹) = (-a)*u⁻¹ := by
    rw [rationalDerivative_inv, ← mul_div_assoc, mul_neg, h]
    field_simp
  have he : R * δ (R^j) = (j : ℂᵣ) * R^j := by
    cases j with
    | ofNat n => simpa using pos n
    | negSucc n =>
      have hc : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
      rw [hc, zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast]
      exact inv (pow_ne_zero _ RatFunc.X_ne_zero) (pos (n+1))
  have hz : R*R^(j-1) = R^j := calc
    _ = R^(1:ℤ)*R^(j-1) := by rw [zpow_one]
    _ = _ := by rw [← zpow_add₀ RatFunc.X_ne_zero, show 1+(j-1)=j by omega]
  apply mul_left_cancel₀ RatFunc.X_ne_zero
  rw [he, mul_left_comm R, hz]

/-- Changing r to 1/r negates the Laurent exponent. -/
theorem reciprocal_radius_zpow (j : ℤ) : reciprocalHom (R^j) = R^(-j) := by
  rw [map_zpow₀, reciprocalHom_radius, inv_zpow, zpow_neg]

theorem laurentToRat_monomial_fraction (j : ℤ) (a : ℂ) (n : ℕ) (hj : 0 ≤ j+(n:ℤ)) :
    laurentToRat (AddMonoidAlgebra.single j a) = ι (monomial (j+(n:ℤ)).toNat a) / ι (X^n) := by
  rw [laurentToRat_single, ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [mul_div_assoc,
    ← zpow_natCast R (j+(n:ℤ)).toNat, Int.toNat_of_nonneg hj,
    ← zpow_natCast R n, ← zpow_sub₀ RatFunc.X_ne_zero, add_sub_cancel_right]

#print axioms laurentToRat_injective
#print axioms rationalDerivative_radius_zpow

end

end SchwarzschildLaurent
