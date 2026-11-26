import ExteriorRationalEvaluation
import OutgoingMixtureInfinity

/-! The rational rows used by the two admitted mixtures have no poles
at a real exterior radius. The forcing is the checked source row
evaluated on the same wave and scaled jet as the particular field. -/
namespace SchwarzschildMixtures.Strain

open Polynomial SchwarzschildLaurent SchwarzschildLaurent.Exterior
open SchwarzschildLaurent.Outgoing SchwarzschildMixtures.OutgoingData

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ

private theorem exterior_polynomial_denominators (n : ℕ) (hn : 2 ≤ n)
    (r : ℝ) (hr : 2 < r) (scalar : ℂ) (hs : scalar ≠ 0) :
    (fieldDenominator scalar n).eval (r : ℂ) ≠ 0 ∧
      (denominatorStep (poles (n : ℂ))).eval (r : ℂ) ≠ 0 := by
  have hn' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have p₁ : 0 < (n:ℝ)-1 := by linarith
  have p₂ : 0 < 2*(n:ℝ)-1 := by linarith
  have rpos : 0 < r := by linarith
  have nr : (r : ℂ) ≠ 0 := by exact_mod_cast rpos.ne'
  have gap : (r : ℂ)-2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hr.ne')
  have parent : (parentPole (n : ℂ)).eval (r : ℂ) ≠ 0 := by
    have p : 0 < r*((n:ℝ)-1)*((n:ℝ)+2)+6 := by positivity
    rw [parentPole,eval_add,eval_mul,eval_X,eval_C,eval_C]
    exact_mod_cast (show r*(((n:ℝ)-1)*((n:ℝ)+2))+6 ≠ 0 by
      rw [← mul_assoc]
      exact p.ne')
  have daughter : (daughterPole (n : ℂ)).eval (r : ℂ) ≠ 0 := by
    have p : 0 < r*(2*(n:ℝ)-1)*((n:ℝ)+1)+3 := by positivity
    rw [daughterPole,eval_add,eval_mul,eval_X,eval_C,eval_C]
    exact_mod_cast (show r*((2*(n:ℝ)-1)*((n:ℝ)+1))+3 ≠ 0 by
      rw [← mul_assoc]
      exact p.ne')
  constructor
  · simp [fieldDenominator,shiftedRadius,hs,nr,gap,parent,daughter]
  · simp [denominatorStep,poles,nr,parent,daughter]

theorem admitted_rows_regular_exterior (second : Bool) (n : ℕ) (hn : 2 ≤ n)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) (r : ℝ) (hr : 2 < r) :
    RegularRow r (admittedField second k n) ∧ RegularRow r (admittedSource second k n) := by
  let m := mixtureMultiplier second
  let q := fieldDenominator (fieldScalar m second k n) n
  let polesStep := denominatorStep (poles (n : ℂ))
  have mpos : 0 < m := by cases second <;> decide
  obtain ⟨hq,hs⟩ := exterior_polynomial_denominators n hn r hr _ (fieldScalar_ne_zero m n mpos hn second k hk ki)
  have hsource : (polesStep*(polesStep*q)).eval (r : ℂ) ≠ 0 := by
    simp only [eval_mul]
    exact mul_ne_zero hs (mul_ne_zero hs hq)
  let forcing := if second then Case2.forcing else Case1.forcing
  have field : admittedField second k n = fractionRow (rowValue k n (mixtureNumerators second)) q := by
    cases second <;> rfl
  have source : admittedSource second k n = fractionRow (rowValue k n forcing) (polesStep*(polesStep*q)) := by
    cases second <;> rfl
  rw [field,source]
  exact ⟨RowValues.fraction _ _ r hq,RowValues.fraction _ _ r hsource⟩

def waveRowValue (p : Row ℂᵣ) (u du : ℝ → ℂ) (r : ℝ) : ℂ :=
  quadraticValue (readRow p r) (u r) (du r)

/-- Evaluate the checked projected regularized source on (J) and
(Z=r^2 D J), in the paper's normalization. -/
def exteriorSource (second : Bool) (n : ℕ) (k : ℂ) (u du : ℝ → ℂ) (r : ℝ) : ℂ :=
  quadraticValue (readRow (admittedSource second k n) r) (u r) ((r : ℂ)^2*du r)

theorem particular_from_unscaled_row (second : Bool) (n : ℕ) (k : ℂ) (u du : ℝ → ℂ) (r : ℝ)
    (h : RegularRow r (admittedField second k n)) :
    waveRowValue (unscaledRow (admittedField second k n)) u du r =
      radialParticular second n k u du r := by
  rw [waveRowValue,h.unscaled.read_eq]
  rfl

theorem source_from_unscaled_row (second : Bool) (n : ℕ) (k : ℂ) (u du : ℝ → ℂ) (r : ℝ)
    (h : RegularRow r (admittedSource second k n)) :
    waveRowValue (unscaledRow (admittedSource second k n)) u du r =
      exteriorSource second n k u du r := by
  rw [waveRowValue,h.unscaled.read_eq]
  simp only [quadraticValue,exteriorSource]
  ring

#print axioms admitted_rows_regular_exterior
#print axioms particular_from_unscaled_row
#print axioms source_from_unscaled_row

end
end SchwarzschildMixtures.Strain
