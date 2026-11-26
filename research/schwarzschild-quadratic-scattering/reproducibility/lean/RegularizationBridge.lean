import RegularizationCaseFields
import MetricMixtureClassification
import MixtureClassification

/-! The forcing calculated from the metric becomes the published
regularized forcing by the operator image of the three actual local
regularizers. The equality holds for the whole quadratic mixture family. -/
namespace SchwarzschildMixtures.Regularization

open SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "L[" n "," k "]" => rationalOperator ((n:ℂ)*(n+1)) ((2*(n:ℂ))*(2*n+1)) k

private theorem first_source_bridge (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    admittedSource false k n =
      plus (metricForcing k n 1 1) (L[n,k] (regularizingField k n 1 1)) := by
  rw [← admitted_field_solves false n hn k hk ki, first_field_bridge n hn k hk ki,
    operator_plus, metric_first_solves n hn k hk ki]
  simp [metricForcing, quadraticSource, plus, scale]

private theorem second_source_bridge (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    let rho := alternativeRatio k n
    admittedSource true k n =
      plus (metricForcing k n 1 rho) (L[n,k] (regularizingField k n 1 rho)) := by
  dsimp only
  rw [← admitted_field_solves true n hn k hk ki, second_field_bridge n hn k hk ki,
    operator_plus, operator_plus, operator_constant_scale,
    metric_first_solves n hn k hk ki, metric_difference_solves n hn k hk ki]
  unfold metricForcing
  rw [second_from_difference]

private theorem odd_source_bridge (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    publishedOdd k n = plus (metricOdd k n) (L[n,k] (regulatorOddOdd k n)) := by
  unfold publishedOdd
  rw [odd_forcing_restored OddCase.multiplier n (by decide +kernel) hn k hk ki OddCase.field
    OddCase.forcing OddCase.odd_a_checked OddCase.odd_b_checked OddCase.odd_c_checked,
    odd_shift_bridge n hn k hk ki, operator_plus,
    metricOdd, PureOddProgram.calculated_odd_source_is_archived n hn k hk ki]
  apply Prod.ext
  · simp [plus, add_assoc, add_comm]
  · apply Prod.ext <;> simp [plus, add_assoc, add_comm]

private theorem quadratic_add (ee eo oo ue uo uu : Row ℂᵣ) (a b : ℂ) :
    quadraticSource (plus ee ue) (plus eo uo) (plus oo uu) a b =
      plus (quadraticSource ee eo oo a b) (quadraticSource ue uo uu a b) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [quadraticSource, plus, scale] <;> ring

theorem metric_to_published_regularization (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (a b : ℂ) :
    publishedForcing k n a b = plus (metricForcing k n a b) (L[n,k] (regularizingField k n a b)) := by
  let e := plus (metricEven k n) (L[n,k] (regulatorEvenEven k n))
  let m := plus (metricMixed k n) (L[n,k] (regulatorEvenOdd k n))
  have odd := odd_source_bridge n hn k hk ki
  have combined (x y : ℂ) :
      quadraticSource e m (publishedOdd k n) x y =
        plus (metricForcing k n x y) (L[n,k] (regularizingField k n x y)) := by
    dsimp only [e, m]
    rw [odd, quadratic_add]
    simp only [metricForcing, regularizingField, quadraticSource, operator_plus, operator_constant_scale]
  have first := (combined 1 1).trans (first_source_bridge n hn k hk ki).symm
  have second := (combined 1 (alternativeRatio k n)).trans (second_source_bridge n hn k hk ki).symm
  exact (published_forcing_from_components k n a b e m
    (alternativeRatio_ne_one n hn k ki) first second).symm.trans (combined a b)

theorem regularization_preserves_local_solvability (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (a b : ℂ) :
    (∃ p : Row ℂᵣ, L[n,k] p = metricForcing k n a b) ↔
      (∃ p : Row ℂᵣ, L[n,k] p = publishedForcing k n a b) := by
  rw [metric_to_published_regularization n hn k hk ki a b]
  let u := regularizingField k n a b
  constructor
  · rintro ⟨p,h⟩
    exact ⟨plus p u, by rw [operator_plus, h]⟩
  · rintro ⟨p,h⟩
    refine ⟨minus p u, ?_⟩
    rw [operator_minus, h]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [minus, plus, u]

#print axioms metric_to_published_regularization
#print axioms regularization_preserves_local_solvability

end
end SchwarzschildMixtures.Regularization
