import RationalLaurent

/-! Formal calculus in the complex rational function field. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative

theorem rationalDerivative_algebraMap (p : ℂ[X]) : δ (ι p) = ι p.derivative := by
  simpa using rationalDerivative_fraction p 1 one_ne_zero

@[simp] theorem rationalDerivative_zero : δ (0 : ℂᵣ) = 0 := by
  simpa using rationalDerivative_algebraMap (0 : ℂ[X])

@[simp] theorem rationalDerivative_one : δ (1 : ℂᵣ) = 0 := by
  simpa using rationalDerivative_algebraMap (1 : ℂ[X])

@[simp] theorem rationalDerivative_constant (a : ℂ) : δ (RatFunc.C a) = 0 := by
  simpa [RatFunc.algebraMap_C] using rationalDerivative_algebraMap (C a)

@[simp] theorem rationalDerivative_radius : δ R = 1 := by
  simpa [RatFunc.algebraMap_X] using rationalDerivative_algebraMap (X : ℂ[X])

theorem rationalDerivative_add (u v : ℂᵣ) : δ (u + v) = δ u + δ v := by
  refine RatFunc.induction_on (P := fun x => δ (x+v) = δ x + δ v) u ?_
  intro a b hb
  refine RatFunc.induction_on (P := fun x => δ (ι a / ι b + x) = δ (ι a / ι b) + δ x) v ?_
  intro c d hd
  have hb' := RatFunc.algebraMap_ne_zero (K := ℂ) hb
  have hd' := RatFunc.algebraMap_ne_zero (K := ℂ) hd
  have huv : ι a / ι b + ι c / ι d = ι (a*d + c*b) / ι (b*d) := by
    simp only [map_add, map_mul]
    field_simp [hb', hd'] <;> ring
  rw [huv, rationalDerivative_fraction _ _ (mul_ne_zero hb hd),
    rationalDerivative_fraction _ _ hb, rationalDerivative_fraction _ _ hd]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, map_add, map_sub, map_mul]
  field_simp [hb', hd'] <;> ring

theorem rationalDerivative_mul (u v : ℂᵣ) : δ (u*v) = δ u*v + u*δ v := by
  refine RatFunc.induction_on (P := fun x => δ (x*v) = δ x*v + x*δ v) u ?_
  intro a b hb
  refine RatFunc.induction_on (P := fun x => δ (ι a / ι b * x) = δ (ι a / ι b)*x + ι a / ι b*δ x) v ?_
  intro c d hd
  have huv : ι a / ι b * (ι c / ι d) = ι (a*c) / ι (b*d) := by simp [map_mul, div_mul_div_comm]
  rw [huv, rationalDerivative_fraction _ _ (mul_ne_zero hb hd),
    rationalDerivative_fraction _ _ hb, rationalDerivative_fraction _ _ hd]
  simp only [Polynomial.derivative_mul, map_add, map_sub, map_mul]
  field_simp [RatFunc.algebraMap_ne_zero hb, RatFunc.algebraMap_ne_zero hd] <;> ring

theorem rationalDerivative_neg (u : ℂᵣ) : δ (-u) = -δ u := by
  have h := rationalDerivative_add u (-u)
  rw [add_neg_cancel, rationalDerivative_zero] at h
  linear_combination -h

theorem rationalDerivative_sub (u v : ℂᵣ) : δ (u-v) = δ u - δ v := by
  rw [sub_eq_add_neg, rationalDerivative_add, rationalDerivative_neg, sub_eq_add_neg]

theorem rationalDerivative_inv (u : ℂᵣ) : δ (u⁻¹) = -δ u / u^2 := by
  by_cases h : u = 0
  · simp [h]
  have hh := rationalDerivative_mul u u⁻¹
  rw [mul_inv_cancel₀ h, rationalDerivative_one] at hh
  have he : u * δ (u⁻¹) = -(δ u * u⁻¹) := by linear_combination -hh
  apply (eq_div_iff (pow_ne_zero 2 h)).2
  calc
    _ = u*(u*δ (u⁻¹)) := by ring
    _ = _ := by rw [he]; field_simp [h] <;> ring

theorem rationalDerivative_div (u v : ℂᵣ) :
    δ (u/v) = (δ u*v-u*δ v)/v^2 := by
  rw [div_eq_mul_inv, rationalDerivative_mul, rationalDerivative_inv]
  by_cases h : v = 0
  · simp [h]
  field_simp [h] <;> ring

theorem rationalDerivative_pow (u : ℂᵣ) (n : ℕ) :
    δ (u^n) = (n : ℂᵣ) * u^(n-1) * δ u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ u n, rationalDerivative_mul, ih]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one, pow_succ]; ring

@[simp] theorem rationalDerivative_baseMap (a : ℂ) :
    δ (algebraMap ℂ ℂᵣ a) = 0 := rationalDerivative_constant a

theorem rationalDerivative_aeval (p : ℂ[X]) (u : ℂᵣ) :
    δ (Polynomial.aeval u p) = Polynomial.aeval u p.derivative * δ u := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add, rationalDerivative_add, ha, hb]
    ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, Polynomial.derivative_C_mul_X_pow]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      rationalDerivative_mul, rationalDerivative_pow, rationalDerivative_baseMap,
      zero_mul, zero_add, map_natCast]
    ring

#print axioms rationalDerivative_add
#print axioms rationalDerivative_mul
#print axioms rationalDerivative_aeval

end

end SchwarzschildLaurent
