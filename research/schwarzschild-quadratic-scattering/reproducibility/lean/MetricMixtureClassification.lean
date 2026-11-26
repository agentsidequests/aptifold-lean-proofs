import MetricBareSolutions
import MixtureSourceAlgebra
import PureOddKernelLink

/-! Exact mixture classification using only the three unregularized
source rows from the metric calculation in the forcing. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def metricForcing (k ell a b : ℂ) : Row ℂᵣ :=
  quadraticSource (metricEven k ell) (metricMixed k ell) (metricOdd k ell) a b

theorem second_from_difference (ee eo oo : Row ℂᵣ) (ρ : ℂ) :
    plus (plus ee (plus eo oo)) (scale (Cᵣ (ρ-1)) (plus eo (scale (Cᵣ (1+ρ)) oo))) =
      quadraticSource ee eo oo 1 ρ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [quadraticSource, scale, plus, one_pow, one_mul,
      map_pow, map_one, map_sub, map_add] <;> ring

theorem metric_mixture_classification (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (a b : ℂ) :
    (∃ p : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k p =
      metricForcing k n a b) ↔ b = a ∨ b = alternativeRatio k n*a := by
  let ρ := alternativeRatio k n
  let first := metricFirstField k n
  let second := plus first (scale (Cᵣ (ρ-1)) (metricDifferenceField k n))
  have h₁ : rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k first = metricForcing k n 1 1 := by
    change rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (metricFirstField k n) = _
    rw [metric_first_solves n hn k hk ki]
    simp [metricForcing, quadraticSource, plus, scale]
  have h₂ : rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k second = metricForcing k n 1 ρ := by
    change rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k
      (plus (metricFirstField k n) (scale (Cᵣ (ρ-1)) (metricDifferenceField k n))) = _
    rw [operator_plus, operator_constant_scale,
      metric_first_solves n hn k hk ki, metric_difference_solves n hn k hk ki]
    exact second_from_difference _ _ _ ρ
  have exclude : ¬ ∃ p : Row ℂᵣ, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k p =
      archivedSource k n := by
    simpa only [Int.cast_natCast] using archived_rational_row_no_solution n hn k hk ki
  have ho := PureOddProgram.calculated_odd_source_is_archived n hn k hk ki
  unfold metricForcing at *
  rw [quadratic_source_factorization _ _ _ ρ a b (alternativeRatio_ne_one n hn k ki)]
  exact exact_roots_of_obstruction _ _ _ ρ a b first second _ _ _ _ _ h₁ h₂ ho exclude

#print axioms metric_mixture_classification

end
end SchwarzschildMixtures
