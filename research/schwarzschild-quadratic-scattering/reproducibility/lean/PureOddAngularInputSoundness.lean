import PureOddAngularCalculation
import PureOddChart

/-! Bind the exact arithmetic input to the full-angle metric jets. -/
namespace SchwarzschildEinstein.PureOdd

open AngularArithmetic AngularCalculation

local notation "Q" => Fraction.constant
local notation "X" => Fraction.indeterminate

variable {K : Type*} [Field K] [CharZero K]

def angleValues (r k ell c : K) (T P : RadialJet K)
    (extra : ℕ → K := fun _ => 0) : ℕ → K
  | 0 => r
  | 1 => c
  | 2 => k
  | 3 => ell
  | 4 => T.val
  | 5 => T.first
  | 6 => T.second
  | 7 => P.val
  | 8 => P.first
  | 9 => P.second
  | n => extra n

noncomputable section

def angularEvaluation (x : ℕ → K) (hr : x 0 ≠ 0) (hh : x 0-2 ≠ 0)
    (hs : sineSquared (x 1) ≠ 0) : Evaluation Fraction K :=
  ⟨Fraction.eval x, Fraction.eval_zero x, Fraction.eval_add x hr hh hs,
    Fraction.eval_neg x, Fraction.eval_mul x⟩

section PointEvaluation

variable (r k ell c : K) (T P : RadialJet K) (extra : ℕ → K)
  (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0)

local notation "x" => angleValues r k ell c T P extra
local notation "e" => angularEvaluation x hr hh hs

include hr hh hs

@[simp] private theorem point_value (f : Fraction) : Evaluation.value e f = f.eval x := rfl

omit hr hh hs in
@[simp] private theorem eval_rInv (n : ℕ) : (rInv n).eval x = 1/r^n := by
  simp [rInv, Denominator.eval, angleValues]

omit hr hh hs in
@[simp] private theorem eval_hInv (n : ℕ) : (hInv n).eval x = 1/(r-2)^n := by
  simp [hInv, Denominator.eval, angleValues]

@[simp] private theorem eval_sin (c' : Fraction) :
    (sin2 c').eval x = sineSquared (c'.eval x) := by
  simp [sin2, Fraction.eval_add x hr hh hs, sineSquared, pow_two, sub_eq_add_neg]

theorem map_zero : Evaluation.second e (axisJet 2 0 0 0) = SecondJet.constant 0 := by
  rw [Evaluation.axis_map]
  simp [point_value, oneAxis, SecondJet.constant, FirstJet.constant]

theorem map_background (c' : Fraction) (a b : Axis) :
    Evaluation.second e (affineBackground c' a b) = fullAngleBackground r (c'.eval x) a b := by
  have zeroAxis := (axis_constant 2 (0:K)).symm
  have sinEval := eval_sin r k ell c T P extra hr hh hs c'
  unfold affineBackground fullAngleBackground
  split_ifs
  all_goals
    norm_num [map_zero, point_value, background, polar, angleValues, Fraction.eval_add x hr hh hs,
      zeroAxis, sinEval, Fin.ext_iff, -Fin.val_eq_zero_iff, pow_two, sub_eq_add_neg, div_eq_mul_inv] <;>
      (congr 1 <;> ring)

theorem map_inverse (c' inverseSine : Fraction)
    (hinv : inverseSine.eval x = 1/sineSquared (c'.eval x)) (a : Axis) :
    Evaluation.first e (affineInverse c' inverseSine a) = fullAngleInverseDiagonal r (c'.eval x) a := by
  all_goals
    fin_cases a <;>
      norm_num [affineInverse, fullAngleInverseDiagonal, inverseDiagonal, ← Evaluation.to_first,
        point_value, hinv, polar, angleValues, Fraction.eval_add x hr hh hs, Fin.ext_iff,
        -Fin.val_eq_zero_iff, pow_two, sub_eq_add_neg, div_eq_mul_inv]
  all_goals
    apply first_jet_ext
    all_goals try (intro i; fin_cases i)
    all_goals
      norm_num [SecondJet.mul, FirstJet.mul, oneAxis, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring

theorem map_carrier (c' : Fraction) :
    Evaluation.second e (affineCarrier c') = fullAngleCarrier k ell (c'.eval x) := by
  have sinEval := eval_sin r k ell c T P extra hr hh hs c'
  apply jet_ext
  · norm_num [affineCarrier, fullAngleCarrier, point_value]
  · intro a
    fin_cases a <;>
      norm_num [affineCarrier, fullAngleCarrier, Evaluation.second, Evaluation.first, point_value,
        angleValues, Fin.ext_iff, -Fin.val_eq_zero_iff]
  · intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [affineCarrier, fullAngleCarrier, Evaluation.second, point_value, angleValues,
        Fin.ext_iff, -Fin.val_eq_zero_iff, Fraction.eval_add x hr hh hs, sub_eq_add_neg, sinEval]

theorem map_parent (c' : Fraction) (a b : Axis) :
    Evaluation.second e (affineParent c' a b) = fullAngleParentMetric k ell (c'.eval x) T P a b := by
  have zeroAxis := (axis_constant 2 (0:K)).symm
  have sinEval := eval_sin r k ell c T P extra hr hh hs c'
  unfold affineParent fullAngleParentMetric
  split_ifs
  all_goals
    norm_num [map_zero, point_value, map_carrier, radial, polar, angleValues,
      Fraction.eval_add x hr hh hs, sub_eq_add_neg, zeroAxis, sinEval]

theorem angular_ricci_evaluation_with (c' inverseSine : Fraction)
    (hinv : inverseSine.eval x = 1/sineSquared (c'.eval x)) (a b : Axis) :
    (angularRicciFractions c' inverseSine a b).eval x =
      fullAngleRicci r k ell (c'.eval x) T P a b := by
  have half : Evaluation.value e (Q (1/2)) = 1/2 := by norm_num [point_value]
  have g : Evaluation.secondMatrix e (affineBackground c') =
      fullAngleBackground r (c'.eval x) :=
    funext fun i => funext (map_background r k ell c T P extra hr hh hs c' i)
  have B : (fun i => Evaluation.first e (affineInverse c' inverseSine i)) =
      fullAngleInverseDiagonal r (c'.eval x) :=
    funext (map_inverse r k ell c T P extra hr hh hs c' inverseSine hinv)
  have H : Evaluation.secondMatrix e (affineParent c') =
      fullAngleParentMetric k ell (c'.eval x) T P :=
    funext fun i => funext (map_parent r k ell c T P extra hr hh hs c' i)
  have proof := Evaluation.ricci_map e (Q (1/2)) (affineBackground c') (affineInverse c' inverseSine)
      (affineParent c') a b half
  rw [g, B, H] at proof
  exact proof

end PointEvaluation

theorem angular_ricci_evaluation (r k ell c : K) (T P : RadialJet K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0) (c' inverseSine : Fraction)
    (hinv : inverseSine.eval (angleValues r k ell c T P) =
      1/sineSquared (c'.eval (angleValues r k ell c T P))) (a b : Axis) :
    (angularRicciFractions c' inverseSine a b).eval (angleValues r k ell c T P) =
      fullAngleRicci r k ell (c'.eval (angleValues r k ell c T P)) T P a b :=
  angular_ricci_evaluation_with r k ell c T P (fun _ => 0) hr hh hs c' inverseSine hinv a b

end
end SchwarzschildEinstein.PureOdd
