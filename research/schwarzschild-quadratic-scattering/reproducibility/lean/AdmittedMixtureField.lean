import AdmittedMixtureDomain

/-! The explicit particular fields and their ingoing-horizon residue test. -/
namespace SchwarzschildMixtures
open Polynomial SchwarzschildLaurent

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)

def localField (field : Row Expr) (multiplier : ℕ) (second : Bool) (k ell : ℂ) : Row ℂᵣ :=
  fractionRow (rowValue k ell field) (fieldDenominator (fieldScalar multiplier second k ell) ell)

def projectedSource (source : Row Expr) (multiplier : ℕ) (second : Bool) (k ell : ℂ) : Row ℂᵣ :=
  fractionRow (rowValue k ell source) (denominatorStep (poles ell) *
    (denominatorStep (poles ell) * fieldDenominator (fieldScalar multiplier second k ell) ell))

theorem localField_solves (field source : Row Expr) (multiplier n : ℕ)
    (hm : 0 < multiplier) (hn : 2 ≤ n) (second : Bool) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (c₀ : Expr.Check (sourceData field).1 source.1)
    (c₁ : Expr.Check (sourceData field).2.1 source.2.1)
    (c₂ : Expr.Check (sourceData field).2.2 source.2.2) :
    rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (localField field multiplier second k n) =
      projectedSource source multiplier second k n := by
  have hs := fieldScalar_ne_zero multiplier n hm hn second k hk ki
  exact source_of_checked_numerators k n _ field source (fieldDenominator_ne_zero _ hs n hn)
    (poles_ne_zero n hn) (Prod.ext (Expr.value_eq_of_check _ _ c₀ k n)
      (Prod.ext (Expr.value_eq_of_check _ _ c₁ k n) (Expr.value_eq_of_check _ _ c₂ k n)))

private theorem horizon_numerator_zero (p : Row Expr) (k ell : ℂ)
    (checked : Expr.Check (horizonData p) (Expr.constant 0)) :
    (rowValue k ell p).1.eval 2 - 4*k*(rowValue k ell p).2.1.eval 2 +
      16*k^2*(rowValue k ell p).2.2.eval 2 = 0 := by
  have h := congrArg (Polynomial.eval (0:ℂ)) (Expr.value_eq_of_check _ _ checked k ell)
  simpa [horizonData, rowValue, mapRow, Expr.value_single, Expr.value_constant] using h

private def regularDenominator (scalar ell : ℂ) : ℂ[X] :=
  C scalar * X^11 * (parentPole ell)^5 * daughterPole ell

private theorem regularDenominator_ne_zero (scalar : ℂ) (hs : scalar ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) : (regularDenominator scalar n).eval 2 ≠ 0 := by
  simp [regularDenominator, eval_mul, eval_pow, hs, parentPole_horizon_ne_zero n hn,
    daughterPole_horizon_ne_zero n hn]

private theorem fieldDenominator_factor (s ell : ℂ) :
    fieldDenominator s ell = localCoordinate 2 * regularDenominator s ell := by
  simp only [fieldDenominator, regularDenominator, localCoordinate, shiftedRadius, map_ofNat]
  ring

private theorem scaled_horizon_value (p : ℂ[X]) (scalar : ℂ) (hs : scalar ≠ 0) (n : ℕ) (hn : 2 ≤ n) :
    RadiusValue 2 (coordinate 2 * (ι p / ι (fieldDenominator scalar n)))
      (p.eval 2 / (regularDenominator scalar n).eval 2) := by
  have hq := regularDenominator_ne_zero scalar hs n hn
  have hq' : regularDenominator scalar n ≠ 0 := by
    intro he
    simp [he] at hq
  have hc : coordinate 2 * (ι p / ι (fieldDenominator scalar n)) =
      ι p / ι (regularDenominator scalar n) := by
    rw [fieldDenominator_factor, map_mul, ← coordinate]
    field_simp [coordinate_ne_zero, RatFunc.algebraMap_ne_zero hq']
  rw [hc]
  exact RadiusValue.fraction _ _ hq

/-- Each coefficient has at most a simple pole and the possible ingoing
residue of the quadratic combination vanishes. -/
theorem ingoing_horizon_residue (p : Row Expr) (multiplier n : ℕ)
    (hm : 0 < multiplier) (hn : 2 ≤ n) (second : Bool) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (checked : Expr.Check (horizonData p) (Expr.constant 0)) :
    let row := localField p multiplier second k n
    ∃ a b c : ℂ, RadiusValue 2 (coordinate 2 * row.1) a ∧
      RadiusValue 2 (coordinate 2 * row.2.1) b ∧ RadiusValue 2 (coordinate 2 * row.2.2) c ∧
      a - 4*k*b + 16*k^2*c = 0 := by
  let s := fieldScalar multiplier second k n
  let v := rowValue k n p
  let q := (regularDenominator s n).eval 2
  have hs := fieldScalar_ne_zero multiplier n hm hn second k hk ki
  refine ⟨v.1.eval 2 / q, v.2.1.eval 2 / q, v.2.2.eval 2 / q,
    scaled_horizon_value _ s hs n hn, scaled_horizon_value _ s hs n hn,
    scaled_horizon_value _ s hs n hn, ?_⟩
  simp only [v, ← mul_div_assoc, ← sub_div, ← add_div, horizon_numerator_zero p k n checked, zero_div]

end
end SchwarzschildMixtures
