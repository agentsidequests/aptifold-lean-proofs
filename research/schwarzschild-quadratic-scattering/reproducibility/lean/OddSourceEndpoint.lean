import MixtureClassification
import OddSourceNumerators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The pure-odd source has regular coefficients at the future horizon.
Its ingoing contraction vanishes there, and each unscaled radial
coefficient has two inverse powers of decay at infinity. -/
namespace SchwarzschildMixtures

open Polynomial SchwarzschildLaurent NumeratorData

noncomputable section

set_option maxRecDepth 12000

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)

private theorem parent_daughter_linear (n : ℕ) (hn : 2 ≤ n) :
    (parentPole (n : ℂ)).natDegree = 1 ∧ (daughterPole (n : ℂ)).natDegree = 1 := by
  have nR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have np : 0 < (n : ℝ)-1 := by linarith
  have nd : 0 < 2*(n : ℝ)-1 := by linarith
  have p : ((n : ℂ)-1)*((n : ℂ)+2) ≠ 0 := by
    exact_mod_cast (show ((n : ℝ)-1)*((n : ℝ)+2) ≠ 0 by positivity)
  have d : (2*(n : ℂ)-1)*((n : ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (2*(n : ℝ)-1)*((n : ℝ)+1) ≠ 0 by positivity)
  have linear (s t : ℂ) (nonzero : s ≠ 0) : (X*C s+C t).natDegree = 1 := by
    have a : (X*C s).natDegree = 1 := by rw [mul_comm,natDegree_C_mul_X s nonzero]
    exact (natDegree_add_eq_left_of_natDegree_lt (by rw [a,natDegree_C]; decide)).trans a
  exact ⟨linear _ _ p,linear _ _ d⟩

private theorem parent_daughter_exterior (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 2 ≤ r) :
    (parentPole (n : ℂ)).eval (r : ℂ) ≠ 0 ∧ (daughterPole (n : ℂ)).eval (r : ℂ) ≠ 0 := by
  have nR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have np : 0 < (n : ℝ)-1 := by linarith
  have nd : 0 < 2*(n : ℝ)-1 := by linarith
  have rpos : 0 ≤ r := by linarith
  constructor
  · rw [parentPole,eval_add,eval_mul,eval_X,eval_C,eval_C]
    exact_mod_cast (show r*(((n : ℝ)-1)*((n : ℝ)+2))+6 ≠ 0 by positivity)
  · rw [daughterPole,eval_add,eval_mul,eval_X,eval_C,eval_C]
    exact_mod_cast (show r*((2*(n : ℝ)-1)*((n : ℝ)+1))+3 ≠ 0 by positivity)

private theorem rowValue_ext (k ell : ℂ) (s : Row Expr) (p : Row ℂ[X])
    (a : Expr.value k ell s.1 = p.1) (b : Expr.value k ell s.2.1 = p.2.1)
    (c : Expr.value k ell s.2.2 = p.2.2) : rowValue k ell s = p :=
  Prod.ext a (Prod.ext b c)

/-- Exact denominator, degree and horizon identities in the unscaled
quadratic basis `(J², J DJ, (DJ)²)`. -/
theorem pure_odd_source_endpoint_data (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    ∃ (p : Row ℂ[X]) (q : ℂ[X]),
      unscaledRow (publishedOdd k n) = fractionRow p q ∧
      (∀ r : ℝ, 2 ≤ r → q.eval (r : ℂ) ≠ 0) ∧
      q.natDegree = 25 ∧ p.1.natDegree ≤ 23 ∧ p.2.1.natDegree ≤ 23 ∧ p.2.2.natDegree ≤ 23 ∧
      p.1.eval 2-k*p.2.1.eval 2+k^2*p.2.2.eval 2 = 0 := by
  let scalar := fieldScalar (oddMultiplier OddCase.multiplier) false k n
  let q := C scalar*X^15*(parentPole (n : ℂ))^7*(daughterPole (n : ℂ))^3
  have scalar0 : scalar ≠ 0 := fieldScalar_ne_zero _ n (by decide +kernel) hn false k hk ki
  have live (r : ℝ) (hr : 2 ≤ r) : q.eval (r : ℂ) ≠ 0 := by
    obtain ⟨p0,d0⟩ := parent_daughter_exterior n hn r hr
    have r0 : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
    simp [q,eval_mul,eval_pow,scalar0,r0,p0,d0]
  have ⟨parentDeg,daughterDeg⟩ := parent_daughter_linear n hn
  have parent0 : parentPole (n : ℂ) ≠ 0 := fun e => by simp [e] at parentDeg
  have daughter0 : daughterPole (n : ℂ) ≠ 0 := fun e => by simp [e] at daughterDeg
  have denomDeg : q.natDegree = 25 := by
    dsimp only [q]
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr scalar0) (pow_ne_zero _ X_ne_zero))
          (pow_ne_zero _ parent0)) (pow_ne_zero _ daughter0),
        natDegree_mul (mul_ne_zero (C_ne_zero.mpr scalar0) (pow_ne_zero _ X_ne_zero))
          (pow_ne_zero _ parent0),
        natDegree_C_mul scalar0,natDegree_X_pow,natDegree_pow,natDegree_pow,parentDeg,daughterDeg]
  obtain ⟨a,b,c,ea,eb,ec,da,db,dc,residue⟩ := odd_source_numerators_at_endpoints k n
  refine ⟨(a,b*X^2,c*X^4),q,?_,live,denomDeg,da,?_,?_,?_⟩
  · have den :
        denominatorStep (poles (n : ℂ)) *
          (denominatorStep (poles (n : ℂ))*fieldDenominator scalar n) = shiftedRadius*q := by
      dsimp only [denominatorStep,poles,fieldDenominator,q]
      ring
    have cancel (x : ℂ[X]) : ι (shiftedRadius*x)/ι (shiftedRadius*q) = ι x/ι q := by
      rw [map_mul,map_mul,mul_div_mul_left]
      exact RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero 2 : shiftedRadius ≠ 0)
    unfold publishedOdd oddForcing projectedSource
    change unscaledRow (fractionRow (rowValue k n OddCase.forcing)
      (denominatorStep (poles (n : ℂ))*(denominatorStep (poles (n : ℂ))*fieldDenominator scalar n))) = _
    have factored : rowValue k n OddCase.forcing = (shiftedRadius*a,shiftedRadius*b,shiftedRadius*c) :=
      rowValue_ext k n OddCase.forcing (shiftedRadius*a,shiftedRadius*b,shiftedRadius*c) ea eb ec
    rw [den,factored]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact cancel a
    · change ι (shiftedRadius*b)/ι (shiftedRadius*q)*R^2 = ι (b*X^2)/ι q
      rw [cancel,map_mul ι b (X^2),map_pow ι X 2,RatFunc.algebraMap_X]
      ring
    · change ι (shiftedRadius*c)/ι (shiftedRadius*q)*R^4 = ι (c*X^4)/ι q
      rw [cancel,map_mul ι c (X^4),map_pow ι X 4,RatFunc.algebraMap_X]
      ring
  · exact natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)
  · exact natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)
  · simp only [eval_mul,eval_pow,eval_X]
    linear_combination residue

#print axioms pure_odd_source_endpoint_data

end
end SchwarzschildMixtures
