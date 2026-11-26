import MetricSourceEvaluation
import MetricBareDenominator
import MetricBareFirstChecks
import MetricBareDifferenceChecks
import MetricBareFirstLinkA
import MetricBareFirstLinkB
import MetricBareFirstLinkC
import MetricBareDifferenceLinkA
import MetricBareDifferenceLinkB
import MetricBareDifferenceLinkC

/-! The two bare particular fields, linked to the metric-derived
sources through checked rational coefficient identities. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent ExactRational NumeratorData MetricBare

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def metricFirstField (k ell : ℂ) : Row ℂᵣ :=
  localField MetricBareFirst.field MetricBareFirst.multiplier false k ell

def metricDifferenceField (k ell : ℂ) : Row ℂᵣ :=
  localField MetricBareDifference.field MetricBareDifference.multiplier true k ell

theorem metric_first_solves (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (metricFirstField k n) =
      plus (metricEven k n) (plus (metricMixed k n) (metricOdd k n)) := by
  have factors := PureOddProgram.physical_divisors_nonzero n hn k ki
  let output : Row Fraction := (MetricWitness.firstA, MetricWitness.firstB, MetricWitness.firstC)
  have field := checked_bare_field n hn k hk ki MetricBareFirst.multiplier (by decide +kernel) false
    MetricBareFirst.field MetricBareFirst.intermediate MetricBareFirst.forcing
    MetricWitness.firstA MetricWitness.firstB MetricWitness.firstC
    MetricBareFirst.step_a_checked MetricBareFirst.step_b_checked MetricBareFirst.step_c_checked
    (checked_row_value k n (metricSecondStep MetricBareFirst.field MetricBareFirst.intermediate)
      MetricBareFirst.forcing MetricBareFirst.source_a_checked
      MetricBareFirst.source_b_checked MetricBareFirst.source_c_checked)
    MetricBareFirst.sourceA_cancellation MetricBareFirst.sourceB_cancellation MetricBareFirst.sourceC_cancellation
  calc
    _ = mapRow (Fraction.value k n) output := field
    _ = mapRow (Formula.value k n) MetricSourcePrograms.first :=
      (PureOddProgram.reduced_row_value k n factors MetricSourcePrograms.first output
        MetricWitness.firstA_reduced MetricWitness.firstB_reduced MetricWitness.firstC_reduced).symm
    _ = _ := metric_first_value k n

theorem metric_difference_solves (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (metricDifferenceField k n) =
      plus (metricMixed k n) (scale (Cᵣ (1+alternativeRatio k n)) (metricOdd k n)) := by
  have factors := PureOddProgram.physical_divisors_nonzero n hn k ki
  let output : Row Fraction :=
    (MetricWitness.differenceA, MetricWitness.differenceB, MetricWitness.differenceC)
  have image := split_metric_image k n MetricBareDifference.field MetricBareDifference.intermediate
    MetricBareDifference.secondStep MetricBareDifference.forcing
    (checked_row_value k n (stepData 13 6 2 MetricBareDifference.intermediate)
      MetricBareDifference.secondStep MetricBareDifference.second_a_checked
      MetricBareDifference.second_b_checked MetricBareDifference.second_c_checked)
    (checked_row_value k n (metricFinish MetricBareDifference.field MetricBareDifference.secondStep)
      MetricBareDifference.forcing MetricBareDifference.source_a_checked
      MetricBareDifference.source_b_checked MetricBareDifference.source_c_checked)
  have field := checked_bare_field n hn k hk ki MetricBareDifference.multiplier (by decide +kernel) true
    MetricBareDifference.field MetricBareDifference.intermediate MetricBareDifference.forcing
    MetricWitness.differenceA MetricWitness.differenceB MetricWitness.differenceC
    MetricBareDifference.step_a_checked MetricBareDifference.step_b_checked MetricBareDifference.step_c_checked
    image
    MetricBareDifference.sourceA_cancellation MetricBareDifference.sourceB_cancellation MetricBareDifference.sourceC_cancellation
  calc
    _ = mapRow (Fraction.value k n) output := field
    _ = mapRow (Formula.value k n) MetricSourcePrograms.difference :=
      (PureOddProgram.reduced_row_value k n factors MetricSourcePrograms.difference output
        MetricWitness.differenceA_reduced MetricWitness.differenceB_reduced MetricWitness.differenceC_reduced).symm
    _ = _ := metric_difference_value k n

#print axioms metric_first_solves
#print axioms metric_difference_solves

end
end SchwarzschildMixtures
