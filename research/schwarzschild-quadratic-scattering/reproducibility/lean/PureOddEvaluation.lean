import PureOddPhysicalDomain
import PureOddFormulaEvaluation

/-! Interpret the exact coefficient certificate at physical angular
labels and common frequencies. -/
namespace SchwarzschildMixtures.PureOddProgram

open Polynomial SchwarzschildLaurent ExactRational

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative

theorem value_interpret (k ell : ℂ) (f : Formula) :
    Formula.value k ell f = Formula.interpret δ R (Cᵣ k) (Cᵣ ell) f := by
  induction f <;> simp only [Formula.value, Formula.interpret, *]

open SchwarzschildEinstein.PureOdd in
theorem reduced_row_value (k ell : ℂ) (d : DivisorsNonzero k ell)
    (input : Quadratic Formula) (output : Quadratic Fraction)
    (a : Reduced input.1 output.1) (b : Reduced input.2.1 output.2.1)
    (c : Reduced input.2.2 output.2.2) :
    mapRow (Formula.value k ell) input = mapRow (Fraction.value k ell) output :=
  Prod.ext (a.sound k ell d).1 (Prod.ext (b.sound k ell d).1 (c.sound k ell d).1)

attribute [local irreducible] coefficients

open SchwarzschildEinstein.PureOdd in
theorem certified_radial_coefficients (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0)
    (output : Quadratic Fraction)
    (a : Reduced coefficients.1 output.1) (b : Reduced coefficients.2.1 output.2.1)
    (c : Reduced coefficients.2.2 output.2.2) :
    bareForcing δ R (Cᵣ k) (Cᵣ (n:ℂ)) = mapRow (Fraction.value k (n:ℂ)) output := by
  let ell : ℂ := n
  have same := congrArg (fun f => mapRow f coefficients) (funext (value_interpret k ell))
  calc
    _ = mapRow (Formula.interpret δ R (Cᵣ k) (Cᵣ ell)) coefficients :=
      (program_value δ R (Cᵣ k) (Cᵣ ell)).symm
    _ = mapRow (Formula.value k ell) coefficients := same.symm
    _ = _ := reduced_row_value k ell (physical_divisors_nonzero n hn k ki) coefficients output a b c

#print axioms certified_radial_coefficients

end
end SchwarzschildMixtures.PureOddProgram
