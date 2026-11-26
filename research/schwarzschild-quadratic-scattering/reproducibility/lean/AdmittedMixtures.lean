
import AdmittedMixtureField
import MeromorphicRadialField
import AdmittedMixtureCase1Checks
import AdmittedMixtureCase2Checks

/-! The two explicit solutions of the projected regularized daughter equation. -/
namespace SchwarzschildMixtures

open SchwarzschildLaurent NumeratorData

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

def mixtureRatio (second : Bool) (k ell : ℂ) : ℂ :=
  if second then alternativeRatio k ell else 1

def admittedField (second : Bool) (k ell : ℂ) : Row ℂᵣ :=
  if second then localField Case2.field Case2.multiplier true k ell
  else localField Case1.field Case1.multiplier false k ell

def admittedSource (second : Bool) (k ell : ℂ) : Row ℂᵣ :=
  if second then projectedSource Case2.forcing Case2.multiplier true k ell
  else projectedSource Case1.forcing Case1.multiplier false k ell

private theorem checked_rows (k ell : ℂ) (p q : ExprRow)
    (a : Expr.Check p.1 q.1) (b : Expr.Check p.2.1 q.2.1) (c : Expr.Check p.2.2 q.2.2) :
    rowValue k ell p = rowValue k ell q :=
  Prod.ext (Expr.value_eq_of_check _ _ a k ell)
    (Prod.ext (Expr.value_eq_of_check _ _ b k ell) (Expr.value_eq_of_check _ _ c k ell))

private theorem checked_operator (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (second : Bool) (m : ℕ) (hm : 0 < m) (field intermediate secondStep source : ExprRow)
    (first : rowValue k n (stepData 11 5 1 field) = rowValue k n intermediate)
    (next : rowValue k n (stepData 13 6 2 intermediate) = rowValue k n secondStep)
    (finish : rowValue k n (MetricBare.metricFinish field secondStep) = rowValue k n source) :
    rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (localField field m second k n) =
      projectedSource source m second k n := by
  have staged : rowValue k n (stepData 13 6 2 (stepData 11 5 1 field)) = rowValue k n secondStep := by
    calc
      _ = rowValue k n (stepData 13 6 2 intermediate) := by
        rw [step_value k n 13 6 2 (stepData 11 5 1 field), step_value k n 13 6 2 intermediate, first]
      _ = _ := next
  have sub_value (p q : ExprRow) : rowValue k n (subData p q) = minus (rowValue k n p) (rowValue k n q) := by
    simp [rowValue, subData, mapRow, minus]
  have image : rowValue k n (sourceData field) = rowValue k n source := by
    simp only [sourceData, MetricBare.metricFinish, sub_value, staged] at finish ⊢
    exact finish
  have hq := fieldDenominator_ne_zero _ (fieldScalar_ne_zero m n hm hn second k hk ki) n hn
  exact source_of_checked_numerators k n _ field source hq (poles_ne_zero n hn) image

theorem admitted_field_solves (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k (admittedField second k n) =
      admittedSource second k n := by
  cases second with
  | false =>
    exact checked_operator n hn k hk ki false Case1.multiplier (by decide)
      Case1.field Case1.intermediate Case1.secondStep Case1.forcing
      (checked_rows _ _ _ _ Case1.step_a_checked Case1.step_b_checked Case1.step_c_checked)
      (checked_rows _ _ _ _ Case1.second_a_checked Case1.second_b_checked Case1.second_c_checked)
      (checked_rows _ _ _ _ Case1.source_a_checked Case1.source_b_checked Case1.source_c_checked)
  | true =>
    exact checked_operator n hn k hk ki true Case2.multiplier (by decide)
      Case2.field Case2.intermediate Case2.secondStep Case2.forcing
      (checked_rows _ _ _ _ Case2.step_a_checked Case2.step_b_checked Case2.step_c_checked)
      (checked_rows _ _ _ _ Case2.second_a_checked Case2.second_b_checked Case2.second_c_checked)
      (checked_rows _ _ _ _ Case2.source_a_checked Case2.source_b_checked Case2.source_c_checked)

theorem two_admitted_mixtures (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    mixtureRatio true k n ≠ mixtureRatio false k n ∧
      ∀ second : Bool, rationalOperator ((n:ℂ)*(n+1)) ((2*n:ℂ)*(2*n+1)) k
        (admittedField second k n) = admittedSource second k n :=
  ⟨alternativeRatio_ne_one n hn k ki, fun second => admitted_field_solves second n hn k hk ki⟩

/-- Evaluate the explicit rational coefficients on a fixed meromorphic
homogeneous parent wave. The resulting scalar solves its daughter equation. -/
theorem meromorphic_admitted_solution (second : Bool) (r : ℂ) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (J : MeromorphicRadial.At r)
    (parent : (MeromorphicRadial.differentialField r).deriv ((MeromorphicRadial.differentialField r).deriv J) =
      (MeromorphicRadial.differentialField r).embed (parentTerm ((n:ℂ)*(n+1)) k)*J) :
    let E := MeromorphicRadial.differentialField r
    let hD := (2*(n:ℂ))*(2*(n:ℂ)+1)
    let daughter := E.evaluateRow J (admittedField second k n)
    E.deriv (E.deriv daughter) - E.embed (Cᵣ (4*k^2)+oddPotential hD)*daughter =
      E.evaluateRow J (admittedSource second k n) := by
  dsimp only
  rw [(MeromorphicRadial.differentialField r).evaluateRow_operator _ _ _ J parent,
    admitted_field_solves second n hn k hk ki]

theorem admitted_horizon_residue (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    let row := admittedField second k n
    ∃ a b c : ℂ, RadiusValue 2 (coordinate 2 * row.1) a ∧
      RadiusValue 2 (coordinate 2 * row.2.1) b ∧ RadiusValue 2 (coordinate 2 * row.2.2) c ∧
      a - 4*k*b + 16*k^2*c = 0 := by
  cases second with
  | false => exact ingoing_horizon_residue _ _ n (by decide) hn false k hk ki Case1.horizon_checked
  | true => exact ingoing_horizon_residue _ _ n (by decide) hn true k hk ki Case2.horizon_checked

#print axioms two_admitted_mixtures
#print axioms meromorphic_admitted_solution
#print axioms admitted_horizon_residue

end
end SchwarzschildMixtures
