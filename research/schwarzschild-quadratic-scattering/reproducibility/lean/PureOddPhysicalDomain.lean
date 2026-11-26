import ExactRationalSoundness
import Mathlib.Tactic.Positivity

/-! The rational denominators in the calculated source are nonzero
for physical angular labels and purely imaginary common frequencies. -/
namespace SchwarzschildMixtures.PureOddProgram

open Polynomial SchwarzschildLaurent ExactRational

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private theorem daughter_gap (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    (n:ℂ)*(n+1)*(2*(n:ℂ)-1)*(2*(n:ℂ)+1)-6*k ≠ 0 := by
  have pr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have n1 : (0 : ℝ) < 2*(n:ℝ)-1 := by linarith
  have ep : (0 : ℝ) < (n:ℝ)*((n:ℝ)+1)*(2*(n:ℝ)-1)*(2*(n:ℝ)+1) := by positivity
  intro h
  have hr := congrArg Complex.re h
  simp [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.mul_im,
    Complex.sub_im, Complex.add_im, ki, -mul_eq_zero] at hr
  exact ep.ne' hr

private theorem shifted_radius_ne : (X - C (2 : ℂ)) ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ℂ)) h
  norm_num at h0

private theorem parent_gap (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    ((n:ℂ)-1)*(n:ℂ)*(n+1)*(n+2)+12*k ≠ 0 := by
  have pr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have pred : (0 : ℝ) < (n:ℝ)-1 := by linarith
  have hp : (0 : ℝ) < ((n:ℝ)-1)*(n:ℝ)*(n+1)*(n+2) := by positivity
  intro h
  have zero := congrArg Complex.re h
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, ki, -mul_eq_zero] at zero
  exact hp.ne' zero

theorem physical_divisors_nonzero (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    DivisorsNonzero k n := by
  have pr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have e0 : (0 : ℝ) < (n : ℝ) := by linarith
  have e1 : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have em : (0 : ℝ) < 2*(n : ℝ)-1 := by linarith
  have ep : (0 : ℝ) < 2*(n : ℝ)+1 := by positivity
  intro p valid
  cases p with
  | integer z =>
    have hz : z ≠ 0 := by simpa [Factor.valid] using valid
    simpa [factorValue, Factor.data, Expr.value_constant, RatFunc.algebraMap_C] using hz
  | radius =>
    simpa [factorValue, Factor.data, NumeratorData.x, Expr.value_single, RatFunc.algebraMap_X]
      using RatFunc.X_ne_zero (K := ℂ)
  | horizon =>
    have nonzero : ι (X - C (2 : ℂ)) ≠ 0 := RatFunc.algebraMap_ne_zero shifted_radius_ne
    simpa [factorValue, Factor.data, NumeratorData.xh, NumeratorData.x, NumeratorData.c,
      Expr.value_single, Expr.value_constant] using nonzero
  | angular =>
    have h : (n : ℂ) ≠ 0 := by exact_mod_cast e0.ne'
    simpa [factorValue, Factor.data, NumeratorData.l, RatFunc.algebraMap_C] using h
  | angularPlus =>
    have h : (n : ℂ)+1 ≠ 0 := by exact_mod_cast e1.ne'
    simpa [factorValue, Factor.data, NumeratorData.l, Expr.value_constant, RatFunc.algebraMap_C]
      using (map_ne_zero Cᵣ).mpr h
  | twiceMinus =>
    have h : 2*(n : ℂ)-1 ≠ 0 := by exact_mod_cast em.ne'
    simpa [factorValue, Factor.data, NumeratorData.u, NumeratorData.l, NumeratorData.c,
      Expr.value_constant, RatFunc.algebraMap_C] using (map_ne_zero Cᵣ).mpr h
  | twicePlus =>
    have h : 2*(n : ℂ)+1 ≠ 0 := by exact_mod_cast ep.ne'
    simpa [factorValue, Factor.data, NumeratorData.u, NumeratorData.l, NumeratorData.c,
      Expr.value_constant, RatFunc.algebraMap_C] using (map_ne_zero Cᵣ).mpr h
  | daughterPole =>
    let pole : ℂ[X] := X * C ((2*(n:ℂ)-1)*(n+1)) + C 3
    have hp : pole ≠ 0 := by
      intro h
      have h0 := congrArg (Polynomial.eval (0 : ℂ)) h
      norm_num [pole] at h0
    have nonzero : ι pole ≠ 0 := RatFunc.algebraMap_ne_zero hp
    simpa [factorValue, Factor.data, NumeratorData.sparseDaughterPole, NumeratorData.u,
      NumeratorData.l, NumeratorData.c, NumeratorData.x, Expr.value_single, Expr.value_constant,
      pole, map_mul, map_add, map_sub] using nonzero
  | daughterGap =>
    simpa [factorValue, Factor.data, NumeratorData.u, NumeratorData.l, NumeratorData.w,
      NumeratorData.c, Expr.value_constant, RatFunc.algebraMap_C, map_mul, map_add, map_sub] using
      (map_ne_zero Cᵣ).mpr (daughter_gap n hn k ki)
  | parentPole =>
    let pole : ℂ[X] := X*C (((n:ℂ)-1)*(n+2)) + C 6
    have hp : pole ≠ 0 := by
      intro h
      have h0 := congrArg (Polynomial.eval (0 : ℂ)) h
      norm_num [pole] at h0
    simpa [factorValue, Factor.data, NumeratorData.sparseParentPole, NumeratorData.l,
      NumeratorData.c, NumeratorData.x, Expr.value_single, Expr.value_constant, pole,
      map_mul, map_add, map_sub] using RatFunc.algebraMap_ne_zero hp
  | parentGap =>
    simpa [factorValue, Factor.data, NumeratorData.l, NumeratorData.w, NumeratorData.c,
      Expr.value_constant, RatFunc.algebraMap_C, map_mul, map_add, map_sub] using
      (map_ne_zero Cᵣ).mpr (parent_gap n hn k ki)
  | sevenMinus =>
    have nr : (0 : ℝ) < 7*(n:ℝ)-1 := by linarith
    have h : 7*(n:ℂ)-1 ≠ 0 := by exact_mod_cast nr.ne'
    simpa [factorValue, Factor.data, NumeratorData.l, Expr.value_constant,
      RatFunc.algebraMap_C, map_mul, map_sub] using (map_ne_zero Cᵣ).mpr h

#print axioms physical_divisors_nonzero

end
end SchwarzschildMixtures.PureOddProgram
