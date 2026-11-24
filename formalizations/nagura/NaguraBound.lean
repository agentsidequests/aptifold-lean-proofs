import Finite
import FactorialBounds
import Valuations

namespace Nagura

open Nat

private theorem reorderEven (c f l : Nat) : c * f * f * l = (f * f) * (c * l) := by
  grind

private theorem evenLcmBound (m : Nat) : runningLcm (2 * m) ≤ 2 ^ (2 * m) * runningLcm m := by
  have ratio := evenLcmDivision (2 * m)
  have half : 2 * m / 2 = m := by omega
  rw [half] at ratio
  have fac : (2 * m)! = (2 * m).choose m * (m !) * (m !) := by
    simpa [show m + m = 2 * m by omega] using factorialSplit m m
  have weight : (2 * m).choose m ≤ 2 ^ (2 * m) := by
    simpa [show m + m = 2 * m by omega] using chooseWeight 1 1 m m
  have facPos : 0 < (m !) * (m !) :=
    Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos m)
  refine Nat.le_of_mul_le_mul_left ?_ facPos
  calc
    ((m !) * (m !)) * runningLcm (2 * m) ≤ (2 * m)! * runningLcm m :=
      Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (runningLcmPos _)) ratio
    _ = ((m !) * (m !)) * ((2 * m).choose m * runningLcm m) := by
      rw [fac]
      exact reorderEven _ _ _
    _ ≤ ((m !) * (m !)) * (2 ^ (2 * m) * runningLcm m) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ weight)

theorem crudeLcm (n : Nat) : runningLcm n ≤ 2 ^ (4 * n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases tiny : n < 2
    · have options : n = 0 ∨ n = 1 := by omega
      rcases options with rfl | rfl <;> decide
    · let m := (n + 1) / 2
      have hm : m < n := by dsimp [m]; omega
      have round : n ≤ 2 * m := by dsimp [m]; omega
      have hexp : 2 * m + 4 * m ≤ 4 * n := by dsimp [m]; omega
      calc
        runningLcm n ≤ runningLcm (2 * m) := runningLcmMono _ _ round
        _ ≤ 2 ^ (2 * m) * runningLcm m := evenLcmBound m
        _ ≤ 2 ^ (2 * m) * 2 ^ (4 * m) := Nat.mul_le_mul_left _ (ih m hm)
        _ = 2 ^ (2 * m + 4 * m) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by decide) hexp

private theorem lowerNumeratorForm (m : Nat) :
    factorialGroup (30 * m) [1, 30] = lowerNumerator m := by
  simp [factorialGroup, lowerNumerator, show 30 * m / 30 = m by omega]

private theorem lowerDenominatorForm (m : Nat) :
    factorialGroup (30 * m) [2, 3, 5] = lowerDenominator m := by
  simp [factorialGroup, lowerDenominator, Nat.mul_assoc,
    show 30 * m / 2 = 15 * m by omega,
    show 30 * m / 3 = 10 * m by omega,
    show 30 * m / 5 = 6 * m by omega]

private theorem lowerDenominatorPos (m : Nat) : 0 < lowerDenominator m :=
  Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)

theorem lowerAtMultiple (m : Nat) (hm : 300 ≤ m) :
    2 ^ (397 * (m - 300)) ≤ runningLcm (30 * m) ^ 10 := by
  have baseDvd := lowerDivision (30 * 300)
  rw [lowerDenominatorForm, lowerNumeratorForm] at baseDvd
  have base : lowerDenominator 300 ≤ lowerNumerator 300 :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) baseDvd
  have boundDvd := lowerLcmDivision (30 * m)
  rw [lowerNumeratorForm, lowerDenominatorForm] at boundDvd
  have posD := lowerDenominatorPos m
  have bound : lowerNumerator m ≤ lowerDenominator m * runningLcm (30 * m) :=
    Nat.le_of_dvd (Nat.mul_pos posD (runningLcmPos _)) boundDvd
  have growth := lowerGrowth base (m - 300)
  have shifted : 300 + (m - 300) = m := by omega
  rw [shifted] at growth
  apply Nat.le_of_mul_le_mul_right _ (Nat.pow_pos (n := 10) posD)
  calc
    2 ^ (397 * (m - 300)) * lowerDenominator m ^ 10 ≤ lowerNumerator m ^ 10 := growth
    _ ≤ (lowerDenominator m * runningLcm (30 * m)) ^ 10 := Nat.pow_le_pow_left bound _
    _ = runningLcm (30 * m) ^ 10 * lowerDenominator m ^ 10 := by
      rw [Nat.mul_pow, Nat.mul_comm]

private theorem upperDenominatorForm (m : Nat) :
    factorialGroup (1806 * m) [2, 3, 7, 43, 1806] = upperDenominator m := by
  simp [factorialGroup, upperDenominator, Nat.mul_assoc,
    show 1806 * m / 2 = 903 * m by omega,
    show 1806 * m / 3 = 602 * m by omega,
    show 1806 * m / 7 = 258 * m by omega,
    show 1806 * m / 43 = 42 * m by omega,
    show 1806 * m / 1806 = m by omega]

theorem upperAtMultiple (m : Nat) : runningLcm (1806 * m) ≤ 2 ^ (2825 * m) := by
  have divides := upperLcmDivision (1806 * m)
  rw [upperDenominatorForm, show 1806 * m / 1806 = m by omega] at divides
  have posD : 0 < upperDenominator m := by
    unfold upperDenominator
    repeat apply Nat.mul_pos
    all_goals exact Nat.factorial_pos _
  have expo : upperBase ^ m ≤ (2 ^ 2821) ^ m :=
    Nat.pow_le_pow_left upperConstant m
  apply Nat.le_of_mul_le_mul_left _ posD
  calc
    upperDenominator m * runningLcm (1806 * m) ≤ (1806 * m)! * runningLcm m :=
      Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (runningLcmPos _)) divides
    _ ≤ (upperDenominator m * upperBase ^ m) * runningLcm m :=
      Nat.mul_le_mul_right _ (upperFactorial m)
    _ = upperDenominator m * (upperBase ^ m * runningLcm m) := Nat.mul_assoc _ _ _
    _ ≤ upperDenominator m * ((2 ^ 2821) ^ m * 2 ^ (4 * m)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul expo (crudeLcm m))
    _ = upperDenominator m * 2 ^ (2825 * m) := by
      rw [← Nat.pow_mul 2 2821 m, ← Nat.pow_add 2]
      exact congrArg (fun e : Nat => upperDenominator m * 2 ^ e)
        (show 2821 * m + 4 * m = 2825 * m by omega)

end Nagura

theorem variant_3969f1f7__h2__h1__h4__h2__h3__h2__h1 : ∀ (x : ℕ), (25 : ℕ) ≤ x → ∃ (p : ℕ), Nat.Prime p ∧ x < p ∧ (5 : ℕ) * p < (6 : ℕ) * x := by
  intro x hx
  by_cases low : x < 2000000
  · exact Nagura.finite x hx low
  · exact Nagura.largeOfBounds (Nagura.upperNormalize Nagura.runningLcmMono Nagura.upperAtMultiple)
      (Nagura.lowerNormalize Nagura.runningLcmMono Nagura.lowerAtMultiple)
      Nagura.crudeLcm Nagura.primePowerCorrection x (by omega)

#print axioms variant_3969f1f7__h2__h1__h4__h2__h3__h2__h1
