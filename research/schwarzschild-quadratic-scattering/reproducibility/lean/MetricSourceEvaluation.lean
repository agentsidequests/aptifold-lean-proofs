import MetricSourcePrograms
import EvenFormulaEvaluation
import PureOddEvaluation
import AdmittedMixtureDomain

/-! Interpret the certified expression programs in the same rational
function field as the daughter operator. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent ExactRational
open SchwarzschildEinstein.PureOdd (bareForcing)

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "δ" => rationalDerivative
local notation "C" => (fun q : Rat => (q : ℂᵣ))

def metricEven (k ell : ℂ) : Row ℂᵣ :=
  SchwarzschildEinstein.PureOdd.Polar.bareEvenRows C δ R (Cᵣ k) (Cᵣ ell)

def metricMixed (k ell : ℂ) : Row ℂᵣ :=
  SchwarzschildEinstein.PureOdd.Mixed.bareMixedRows C δ R (Cᵣ k) (Cᵣ ell)

def metricOdd (k ell : ℂ) : Row ℂᵣ :=
  bareForcing δ R (Cᵣ k) (Cᵣ ell)

private theorem gamma_value (k ell z : ℂ) (f : Formula) (h : f.value k ell = Cᵣ z) :
    (MetricSourcePrograms.gammaFormula f).value k ell = Cᵣ (gamma z) := by
  change ((f - .integer 1)*f*(f + .integer 1)*(f + .integer 2)/.integer 12).value k ell = _
  simp [Formula.value_sub, Formula.value, gamma, h, map_div₀, map_ofNat]

private theorem ratio_value (k ell : ℂ) :
    (MetricSourcePrograms.ratio .frequency .angular).value k ell = Cᵣ (alternativeRatio k ell) := by
  let g := MetricSourcePrograms.gammaFormula .angular
  let G := MetricSourcePrograms.gammaFormula (Formula.integer 2 * Formula.angular) / Formula.integer 2
  change ((G+g)*(g-Formula.frequency)/((G-g)*(g+Formula.frequency))).value k ell = _
  have h : (Formula.integer 2 * Formula.angular).value k ell = Cᵣ (2*ell) := by
    simp [Formula.value, map_ofNat]
  simp only [g, G, Formula.value_mul, Formula.value_sub, Formula.value_add,
    Formula.value_div, gamma_value k ell ell .angular rfl, gamma_value k ell _ _ h, Formula.value]
  simp [daughterGamma, alternativeRatio, map_div₀, map_ofNat]

private theorem even_value (k ell : ℂ) :
    mapRow (Formula.value k ell) SchwarzschildEinstein.PureOdd.Polar.coefficients = metricEven k ell := by
  rw [show Formula.value k ell = _ from funext (PureOddProgram.value_interpret k ell)]
  exact SchwarzschildEinstein.PureOdd.Polar.even_program_value δ R (Cᵣ k) (Cᵣ ell)

private theorem mixed_value (k ell : ℂ) :
    mapRow (Formula.value k ell) SchwarzschildEinstein.PureOdd.Mixed.coefficients = metricMixed k ell := by
  rw [show Formula.value k ell = _ from funext (PureOddProgram.value_interpret k ell)]
  exact SchwarzschildEinstein.PureOdd.Mixed.mixed_program_value δ R (Cᵣ k) (Cᵣ ell)

private theorem odd_value (k ell : ℂ) :
    mapRow (Formula.value k ell) PureOddProgram.coefficients = metricOdd k ell := by
  rw [show Formula.value k ell = _ from funext (PureOddProgram.value_interpret k ell)]
  exact PureOddProgram.program_value δ R (Cᵣ k) (Cᵣ ell)

private theorem evaluate_plus (k ell : ℂ) (a b : Row Formula) :
    mapRow (Formula.value k ell) (plus a b) =
      plus (mapRow (Formula.value k ell) a) (mapRow (Formula.value k ell) b) := rfl

private theorem evaluate_scale (k ell : ℂ) (a : Formula) (b : Row Formula) :
    mapRow (Formula.value k ell) (scale a b) =
      scale (a.value k ell) (mapRow (Formula.value k ell) b) := rfl

theorem metric_first_value (k ell : ℂ) :
    mapRow (Formula.value k ell) MetricSourcePrograms.first =
      plus (metricEven k ell) (plus (metricMixed k ell) (metricOdd k ell)) := by
  change mapRow (Formula.value k ell) (plus _ (plus _ _)) = _
  rw [evaluate_plus, evaluate_plus, even_value, mixed_value, odd_value]

theorem metric_difference_value (k ell : ℂ) :
    mapRow (Formula.value k ell) MetricSourcePrograms.difference =
      plus (metricMixed k ell) (scale (Cᵣ (1+alternativeRatio k ell)) (metricOdd k ell)) := by
  change mapRow (Formula.value k ell) (plus _ (scale _ _)) = _
  rw [evaluate_plus, evaluate_scale, mixed_value, odd_value, Formula.value_add, ratio_value]
  simp [Formula.value]

#print axioms metric_first_value
#print axioms metric_difference_value

end
end SchwarzschildMixtures
