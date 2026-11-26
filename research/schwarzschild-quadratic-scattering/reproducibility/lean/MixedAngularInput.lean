import MixedSourceReadouts
import PureOddAngularInputSoundness

/-! Bind the mixed angular arithmetic to the polar and axial metric
jets. Free radial jets allow the angular result to be reused with either
parent master variable. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open AngularArithmetic AngularCalculation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

def extraValues (E : PolarParentJets K) : ℕ → K
  | 10 => E.tt.val
  | 11 => E.tt.first
  | 12 => E.tt.second
  | 13 => E.tr.val
  | 14 => E.tr.first
  | 15 => E.tr.second
  | 16 => E.rr.val
  | 17 => E.rr.first
  | 18 => E.rr.second
  | 19 => E.sphere.val
  | 20 => E.sphere.first
  | 21 => E.sphere.second
  | _ => 0

def polarMetric (k ell c : K) (E : PolarParentJets K) : SecondMetric K :=
  let Y := fullAngleCarrier k ell c
  let s := sineSquared c
  let vv := polar s (2*(c-1)*s) ((4*c^2-10*c+6-2*s)*s)
  let qq := polar (-s) (-(2*c*s)) (-(2*(2*c^2-c-s)*s))
  fun a b =>
    if a = 0 ∧ b = 0 then (radial E.tt).mul Y
    else if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then (radial E.tr).mul Y
    else if a = 1 ∧ b = 1 then (radial E.rr).mul Y
    else if a = 2 ∧ b = 2 then (radial E.sphere).mul (Y.mul vv)
    else if a = 3 ∧ b = 3 then (radial E.sphere).mul (Y.mul qq)
    else SecondJet.constant 0

def ricciValue (r k ell c : K) (T P : RadialJet K) (E : PolarParentJets K)
    (a b : Axis) : K :=
  let g := fullAngleBackground r c
  let B := fullAngleBackgroundInverse r c
  let even := polarMetric k ell c E
  let odd := fullAngleParentMetric k ell c T P
  quadraticJetRicci g B (fun i j => (even i j).add (odd i j)) a b -
    quadraticJetRicci g B even a b - quadraticJetRicci g B odd a b

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

variable (r k ell c : K) (T P : RadialJet K) (E : PolarParentJets K)
variable (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0)

local notation "x" => angleValues r k ell c T P (extraValues E)
local notation "e" => angularEvaluation x hr hh hs

include hr hh hs

@[simp] private theorem value_apply (a : Fraction) : Evaluation.value e a = a.eval x := rfl

theorem map_polar (angle : Fraction) (a b : Axis) :
    Evaluation.second e (polarParent angle a b) = polarMetric k ell (angle.eval x) E a b := by
  have carrier := map_carrier r k ell c T P (extraValues E) hr hh hs angle
  have zero := map_zero r k ell c T P (extraValues E) hr hh hs
  have sine : (sin2 angle).eval x = sineSquared (angle.eval x) := by
    simp [sin2, Fraction.eval_add x hr hh hs, sineSquared, pow_two, sub_eq_add_neg]
  unfold polarParent polarMetric
  split_ifs
  all_goals
    norm_num [carrier, zero, sine, value_apply, Fraction.eval_add x hr hh hs,
      angleValues, extraValues, polar, radial, sub_eq_add_neg, pow_two, mul_assoc]

private theorem map_add (A B : SecondJet Fraction) :
    Evaluation.second e (addJets A B) = (Evaluation.second e A).add (Evaluation.second e B) := by
  simp [Evaluation.second, addJets, SecondJet.add, Fraction.eval_add x hr hh hs]

theorem mixed_ricci_evaluation_at (angle u : Fraction)
    (hu : u.eval x = 1/sineSquared (angle.eval x)) (a b : Axis) :
    (mixedRicci angle u a b).eval x = ricciValue r k ell (angle.eval x) T P E a b := by
  let g := affineBackground angle
  let B := affineInverse angle u
  let Pm := polarParent angle
  let Am := affineParent angle
  have hG : Evaluation.secondMatrix e g = fullAngleBackground r (angle.eval x) := by
    funext a b
    simpa only [g, Evaluation.secondMatrix, Fraction.eval_indeterminate, angleValues] using
      map_background r k ell c T P (extraValues E) hr hh hs angle a b
  have hB : (fun a => Evaluation.first e (B a)) = fullAngleInverseDiagonal r (angle.eval x) := by
    funext a
    simpa only [B, Fraction.eval_indeterminate, angleValues] using
      map_inverse r k ell c T P (extraValues E) hr hh hs angle u hu a
  have hP : Evaluation.secondMatrix e Pm = polarMetric k ell (angle.eval x) E :=
    funext fun a => funext (map_polar r k ell c T P E hr hh hs angle a)
  have hA : Evaluation.secondMatrix e Am = fullAngleParentMetric k ell (angle.eval x) T P := by
    funext a b
    simpa only [Am, Evaluation.secondMatrix, Fraction.eval_indeterminate, angleValues] using
      map_parent r k ell c T P (extraValues E) hr hh hs angle a b
  have hPair : Evaluation.secondMatrix e (fun a b => addJets (Pm a b) (Am a b)) =
      fun a b => (polarMetric k ell (angle.eval x) E a b).add
        (fullAngleParentMetric k ell (angle.eval x) T P a b) := by
    funext a b
    rw [Evaluation.secondMatrix, map_add r k ell c T P E hr hh hs]
    change (Evaluation.secondMatrix e Pm a b).add (Evaluation.secondMatrix e Am a b) = _
    rw [hP,hA]
  have hCalc (H : SecondMetric Fraction) :
      (AngularCalculation.ricci (Q (1/2)) g B H a b).eval x =
        quadraticJetRicci (fullAngleBackground r (angle.eval x))
          (fullAngleBackgroundInverse r (angle.eval x))
          (Evaluation.secondMatrix e H) a b := by
    have half : Evaluation.value e (Q (1/2)) = 1/2 := by norm_num
    have check := Evaluation.ricci_map e (Q (1/2)) g B H a b half
    rw [hG, hB] at check
    exact check
  calc
    _ = (AngularCalculation.ricci (Q (1/2)) g B (fun a b => addJets (Pm a b) (Am a b)) a b).eval x -
        (AngularCalculation.ricci (Q (1/2)) g B Pm a b).eval x -
        (AngularCalculation.ricci (Q (1/2)) g B Am a b).eval x := by
      simp only [mixedRicci, mixedParts, g, B, Pm, Am, AngularCalculation.ricci,
        Fraction.eval_add x hr hh hs, Fraction.eval_neg]
      ring
    _ = _ := by simp only [hCalc, hPair, hP, hA, ricciValue]

theorem predicted_polar_evaluation (a : Axis) :
    (predictedPolar a).eval x =
      (2*ell)*(if a = 0 then (vectorValue r k ell T P E).time else (vectorValue r k ell T P E).radius) := by
  have rInvEval : (rInv 1).eval x = 1/r := by
    simp [rInv, Denominator.eval, angleValues]
  have hInvEval : (hInv 1).eval x = 1/(r-2) := by
    simp [hInv, Denominator.eval, angleValues]
  have mapped :
      symbolicVector.time.eval x = (vectorValue r k ell T P E).time ∧
      symbolicVector.radius.eval x = (vectorValue r k ell T P E).radius := by
    constructor <;>
      norm_num [symbolicVector, vectorValue, vectorCoefficients, radialSymbols, rInvEval, hInvEval,
        Fraction.eval_add x hr hh hs, angleValues, extraValues, lapse, sub_eq_add_neg, div_eq_mul_inv]
  by_cases h : a = 0 <;> simp [predictedPolar, angleValues, h, mapped.1, mapped.2]

omit hr hh hs in
theorem equator_ricci_evaluation (hr' : r ≠ 0) (hh' : r-2 ≠ 0) (a b : Axis) :
    (atEquator a b).eval (angleValues r k ell 0 T P (extraValues E)) =
      ricciValue r k ell 0 T P E a b := by
  have nonzero : sineSquared (0 : K) ≠ 0 := by norm_num [sineSquared]
  have inverse : (Q 1).eval (angleValues r k ell 0 T P (extraValues E)) =
      1/sineSquared ((Q 0).eval (angleValues r k ell 0 T P (extraValues E))) := by
    norm_num [sineSquared]
  simpa [atEquator] using
    mixed_ricci_evaluation_at r k ell 0 T P E hr' hh' nonzero (Q 0) (Q 1) inverse a b

end
end SchwarzschildEinstein.PureOdd.Mixed
