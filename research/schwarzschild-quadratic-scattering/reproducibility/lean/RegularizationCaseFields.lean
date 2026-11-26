import RegularizationFieldAlgebra
import RegularizationCompareFirstChecks
import RegularizationCompareSecondChecks
import RegularizationCompareOddChecks
import AdmittedMixtures
import MetricBareSolutions
import MixtureSourceAlgebra
import RegularizedOddSource

/-! The checked numerator identities connect the actual regulator rows
from the published convention to the two particular fields and odd shift. -/
namespace SchwarzschildMixtures.Regularization

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def regulatorEvenEven (k ell : ℂ) : Row ℂᵣ :=
  localField evenEven regulatorMultiplier false k ell

def regulatorEvenOdd (k ell : ℂ) : Row ℂᵣ :=
  localField evenOdd regulatorMultiplier false k ell

def regulatorOddOdd (k ell : ℂ) : Row ℂᵣ :=
  localField oddOdd regulatorMultiplier false k ell

def regularizingField (k ell a b : ℂ) : Row ℂᵣ :=
  quadraticSource (regulatorEvenEven k ell) (regulatorEvenOdd k ell) (regulatorOddOdd k ell) a b

theorem first_field_bridge (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    admittedField false k n = plus (metricFirstField k n) (regularizingField k n 1 1) := by
  have cert : RowCheck comparisonFirst := ⟨checkedFirstA, checkedFirstB, checkedFirstC⟩
  have eq := compare_base_fields n hn k hk ki Case1.field MetricBareFirst.field
    (addData evenEven (addData evenOdd oddOdd)) Case1.multiplier MetricBareFirst.multiplier regulatorMultiplier
    (by decide +kernel) (by decide +kernel) (by decide +kernel) cert
  simpa only [admittedField, Bool.false_eq_true, if_false, metricFirstField, regularizingField,
    regulatorEvenEven, regulatorEvenOdd, regulatorOddOdd, quadraticSource, one_pow, one_mul,
    map_one, scale, one_mul, local_field_add, Prod.eta] using eq

theorem second_field_bridge (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    let rho := alternativeRatio k n
    admittedField true k n =
      plus (plus (metricFirstField k n) (scale (Cᵣ (rho-1)) (metricDifferenceField k n)))
        (regularizingField k n 1 rho) := by
  have cert : RowCheck comparisonSecond := ⟨checkedSecondA, checkedSecondB, checkedSecondC⟩
  have eq := compare_second_fields n hn k hk ki Case2.field MetricBareFirst.field MetricBareDifference.field
    evenEven evenOdd oddOdd Case2.multiplier MetricBareFirst.multiplier MetricBareDifference.multiplier
    regulatorMultiplier (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cert
  simpa only [admittedField, if_true, metricFirstField, metricDifferenceField, regularizingField,
    regulatorEvenEven, regulatorEvenOdd, regulatorOddOdd, quadraticSource, one_pow, one_mul,
    map_one, map_sub, map_pow, scale, plus, one_mul, add_assoc] using eq

theorem odd_shift_bridge (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    oddShift OddCase.multiplier OddCase.field k n =
      plus (oddShift OddBareCase.multiplier OddBareCase.field k n) (regulatorOddOdd k n) := by
  have cert : RowCheck comparisonOdd := ⟨checkedOddA, checkedOddB, checkedOddC⟩
  exact compare_base_fields n hn k hk ki OddCase.field OddBareCase.field oddOdd
    (oddMultiplier OddCase.multiplier) (oddMultiplier OddBareCase.multiplier) regulatorMultiplier
    (by decide +kernel) (by decide +kernel) (by decide +kernel) cert

#print axioms first_field_bridge
#print axioms second_field_bridge
#print axioms odd_shift_bridge

end
end SchwarzschildMixtures.Regularization
