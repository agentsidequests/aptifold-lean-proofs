
import MixturePolynomials
import NormalizedRowOperator

/-! Substitution into the rational daughter equation using a shared denominator. -/
namespace SchwarzschildMixtures

open Polynomial SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative

def derivativeWeight (b : ℂ[X]) : ℂ[X] := X * shiftedRadius * b
def denominatorStep (b : ℂ[X]) : ℂ[X] := X^2 * b

def stepNumerator (h k : ℂ) (b rate : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  plus (scale (derivativeWeight b) (mapRow Polynomial.derivative p))
    (minus (scale b (jetNumerator h k p)) (scale rate p))

theorem fraction_step (h k : ℂ) (q b rate : ℂ[X]) (p : Row ℂ[X])
    (hq : q ≠ 0) (hb : b ≠ 0)
    (hlog : derivativeWeight b * q.derivative = rate * q) :
    rationalStep h k (fractionRow p q) =
      fractionRow (stepNumerator h k b rate p) (denominatorStep b * q) := by
  have hq' := RatFunc.algebraMap_ne_zero hq
  have hb' := RatFunc.algebraMap_ne_zero hb
  have hlog' := congrArg ι hlog
  simp only [derivativeWeight, shiftedRadius, map_mul, map_sub, RatFunc.algebraMap_X,
    map_ofNat] at hlog'
  have deriv_eq (u : ℂ[X]) :
      radialFactor * δ (ι u / ι q) =
      (R*(R-2)*ι b*ι u.derivative - ι rate*ι u)/(R^2*ι b*ι q) := by
    rw [rationalDerivative_div, rationalDerivative_algebraMap, rationalDerivative_algebraMap]
    simp only [radialFactor]
    field_simp [RatFunc.X_ne_zero, hq', hb']
    linear_combination -ι u * hlog'
  apply Prod.ext
  · simp only [rationalStep, fractionRow, stepNumerator, scale, plus, minus,
      rationalRowDerivative, mapRow, jetNumerator, jet, deriv_eq, derivativeWeight,
      denominatorStep, shiftedRadius, map_mul, map_pow, map_sub, map_add,
      RatFunc.algebraMap_X, map_ofNat, map_one]
    field_simp [RatFunc.X_ne_zero, hq', hb']
    ring
  · apply Prod.ext <;> simp only [rationalStep, fractionRow, stepNumerator, scale, plus, minus,
      rationalRowDerivative, mapRow, jetNumerator, jet, deriv_eq, derivativeWeight,
      denominatorStep, shiftedRadius, map_mul, map_pow, map_sub, map_add,
      RatFunc.algebraMap_X, map_ofNat, map_one] <;>
    field_simp [RatFunc.X_ne_zero, hq', hb'] <;> ring

def secondRate (b rate : ℂ[X]) : ℂ[X] :=
  rate + 2*shiftedRadius*b + derivativeWeight b.derivative

private theorem secondRate_correct (q b rate : ℂ[X])
    (hlog : derivativeWeight b * q.derivative = rate * q) :
    derivativeWeight b * (denominatorStep b * q).derivative =
      secondRate b rate * (denominatorStep b * q) := by
  have h := congrArg (fun x => X^2*b*x) hlog
  simp only [derivativeWeight] at h
  simp only [secondRate, denominatorStep, derivative_mul, derivative_pow, derivative_X,
    Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one, derivativeWeight, map_ofNat]
  linear_combination h

def operatorNumerator (h hD k : ℂ) (b rate : ℂ[X]) (p : Row ℂ[X]) : Row ℂ[X] :=
  minus (stepNumerator h k b (secondRate b rate) (stepNumerator h k b rate p))
    (scale (b^2 * daughterNumerator hD k) p)

theorem fraction_operator (h hD k : ℂ) (q b rate : ℂ[X]) (p : Row ℂ[X])
    (hq : q ≠ 0) (hb : b ≠ 0)
    (hlog : derivativeWeight b * q.derivative = rate * q) :
    rationalOperator h hD k (fractionRow p q) =
      fractionRow (operatorNumerator h hD k b rate p)
        (denominatorStep b * (denominatorStep b * q)) := by
  have ht : denominatorStep b ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hb
  rw [rationalOperator, fraction_step h k q b rate p hq hb hlog,
    fraction_step h k _ b (secondRate b rate) _ (mul_ne_zero ht hq) hb
      (secondRate_correct q b rate hlog)]
  rw [operatorNumerator, fractionRow_minus]
  have daughter : ι (daughterNumerator hD k) = R^4*(RatFunc.C (4*k^2)+oddPotential hD) := by
    simp only [daughterNumerator, shiftedRadius, map_mul, map_add, map_sub, map_pow,
      RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat, oddPotential, radialFactor]
    field_simp [RatFunc.X_ne_zero]
  have cancel (u : ℂ[X]) :
      ι (b^2 * daughterNumerator hD k * u) / ι (denominatorStep b * (denominatorStep b * q)) =
      (RatFunc.C (4*k^2)+oddPotential hD)*(ι u/ι q) := by
    simp only [map_mul, map_pow, daughter, denominatorStep, RatFunc.algebraMap_X]
    field_simp [RatFunc.X_ne_zero, RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hb]
  simp only [scale, fractionRow, cancel]

end
end SchwarzschildMixtures
