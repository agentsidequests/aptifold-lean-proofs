import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The signed spin-two phase contribution to the first correction to
the second-mixture strain. These statements concern the exact coefficients
of the linear phase expansion. -/
namespace SchwarzschildMixtures.Strain

noncomputable section

def spinTwoAngularCorrection (j : ℝ) : ℝ :=
  let L := j*(j+1)
  (-(15*L^2+13*L+24))/(2*L*(4*L-3)*(2*j+1))

theorem angular_correction_from_recurrence (j : ℝ) (hj : 2 ≤ j) :
    spinTwoAngularCorrection j =
      (-2-4/(j*(j+1))
        +((j+1)^2-4)^2/((2*j+1)*(2*j+2)*(2*j+3))
        -(j^2-4)^2/((2*j-1)*(2*j)*(2*j+1)))/(2*j+1) := by
  unfold spinTwoAngularCorrection
  dsimp only
  rw [show 4*(j*(j+1))-3 = (2*j-1)*(2*j+3) by ring]
  field_simp (disch := first | positivity | linarith)
  ring

def angularPhaseDifference (j : ℝ) : ℝ :=
  spinTwoAngularCorrection j-2*spinTwoAngularCorrection (2*j)

def cubicSignPolynomial (j : ℝ) : ℝ :=
  80*j^5-188*j^4-497*j^3-754*j^2-378*j+27

private theorem cubic_sign_factorization (j : ℝ) (hj : 2 ≤ j) :
    angularPhaseDifference j =
      3*cubicSignPolynomial j/(2*(4*j+3)*(4*j+1)*(2*j+3)*(2*j-1)*(j+1)*(4*j-1)*(2*j+1)) := by
  have base : 4*(j*(j+1))-3 = (2*j-1)*(2*j+3) := by ring
  have double : 4*(2*j*(2*j+1))-3 = (4*j-1)*(4*j+3) := by ring
  unfold angularPhaseDifference spinTwoAngularCorrection cubicSignPolynomial
  dsimp only
  rw [base,double]
  field_simp (disch := first | positivity | linarith)
  ring

theorem cubic_phase_shift_negative (n : ℕ) (hn : 2 ≤ n) (small : n ≤ 4) :
    angularPhaseDifference (n:ℝ) < 0 := by
  interval_cases n <;> norm_num [angularPhaseDifference,spinTwoAngularCorrection]

theorem cubic_phase_shift_positive (j : ℝ) (hj : 5 ≤ j) :
    0 < angularPhaseDifference j := by
  rw [cubic_sign_factorization j (by linarith)]
  let m := j-5
  have m0 : 0 ≤ m := sub_nonneg.mpr hj
  have numerator : cubicSignPolynomial j =
      80*m^5+1812*m^4+15743*m^3+63591*m^2+110807*m+49662 := by
    unfold cubicSignPolynomial m
    ring
  rw [numerator]
  have d : 0 < 2*j-1 := by linarith
  have f : 0 < 4*j-1 := by linarith
  have j0 : 0 < j := by linarith
  positivity

theorem angular_phase_difference_four_five :
    angularPhaseDifference 4 = -(257:ℝ)/248710 ∧
      angularPhaseDifference 5 = (2759:ℝ)/2624622 := by
  norm_num [angularPhaseDifference,spinTwoAngularCorrection]

#print axioms angular_correction_from_recurrence
#print axioms cubic_phase_shift_negative
#print axioms cubic_phase_shift_positive
#print axioms angular_phase_difference_four_five

end
end SchwarzschildMixtures.Strain
