import ReconstructionTensorChecks
import VacuumJetEvaluation

/-! Interpret the exact Ricci checks after angular differentiation.
Trace reversal is an involution in this four-dimensional chart. -/
namespace SchwarzschildEinstein.PureOdd.Master

open AngularArithmetic AngularCalculation
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def reggeWheelerChartMetric (w m c : K) (T P : RadialJet K)
    (E : Mixed.PolarParentJets K) : SecondMetric K :=
  fun a b => (Mixed.polarMetric w m c E a b).add (fullAngleParentMetric w m c T P a b)

private def metricValues (r c : K) : Tensor Axis K :=
  fun a b => (fullAngleBackground r c a b).value

private def inverseValues (r c : K) : Tensor Axis K :=
  fun a b => (fullAngleBackgroundInverse r c a b).value

def linearChartEinstein (r c : K) (H : SecondMetric K) : Tensor Axis K :=
  einstein (1/2) (metricValues r c) (inverseValues r c)
    (Vacuum.linearJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c) H)

def chartSourceTensor (m c : K) (s : ModeSource K) : Tensor Axis K :=
  Matrix.of (modeTensor (fun q => (q : K)) m c s)

omit [CharZero K] in
private theorem diagonal_trace (r c : K) (A : Tensor Axis K) :
    contraction (inverseValues r c) A =
      (inverseValues r c) 0 0*A 0 0 + (inverseValues r c) 1 1*A 1 1 +
      (inverseValues r c) 2 2*A 2 2 + (inverseValues r c) 3 3*A 3 3 := by
  norm_num [contraction, sum_axes, inverseValues, fullAngleBackgroundInverse, jetDiagonal,
    FirstJet.constant, Fin.ext_iff, -Fin.val_eq_zero_iff]

omit [CharZero K] in
private theorem chart_trace (r c : K) (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0) :
    contraction (inverseValues r c) (metricValues r c) = 4 := by
  rw [diagonal_trace]
  norm_num [metricValues, inverseValues, fullAngleBackground, fullAngleBackgroundInverse,
    fullAngleInverseDiagonal, jetDiagonal, background, inverseDiagonal, SecondJet.mul, FirstJet.mul,
    polar, oneAxis, Fin.ext_iff, -Fin.val_eq_zero_iff]
  generalize s_eq : sineSquared c = s at hs ⊢
  field_simp [hr, hh, hs]
  ring

private theorem harmonic_trace (r m c : K) (s : ModeSource K)
    (hr : r ≠ 0) (hs : sineSquared c ≠ 0) :
    contraction (inverseValues r c) (chartSourceTensor m c s) =
      modeTrace (fun q => (q : K)) r (1/r) (1/(r-2)) s := by
  rw [diagonal_trace]
  norm_num [inverseValues, fullAngleBackgroundInverse, fullAngleInverseDiagonal, jetDiagonal,
    inverseDiagonal, SecondJet.mul, FirstJet.mul, polar, oneAxis, chartSourceTensor, Matrix.of_apply,
    modeTensor, modeTrace,
    Fin.ext_iff, -Fin.val_eq_zero_iff, sineSquared, pow_two, sub_eq_add_neg]
  unfold sineSquared at hs
  rw [pow_two, sub_eq_add_neg] at hs
  generalize s_eq : 1 + -(c*c) = u at hs ⊢
  field_simp [hr, hs]
  ring

private theorem trace_reversal_twice (r c : K) (A : Tensor Axis K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0) :
    let g := metricValues r c
    let B := inverseValues r c
    einstein (1/2) g B (einstein (1/2) g B A) = A := by
  let g := metricValues r c
  let B := inverseValues r c
  let tr := contraction B A
  have splitTrace : contraction B (einstein (1/2) g B A) =
      tr - (1/2)*tr*contraction B g := by
    simp only [diagonal_trace, einstein, tr, B, g]
    ring
  have negTrace : contraction B (einstein (1/2) g B A) = -tr := by
    rw [splitTrace, chart_trace r c hr hh hs]
    ring
  change einstein (1/2) g B (einstein (1/2) g B A) = A
  funext a b
  change A a b - (1/2)*(g a b*tr) -
    (1/2)*(g a b*contraction B (einstein (1/2) g B A)) = _
  rw [negTrace]
  ring

private theorem coordinate_ricci_certificate (a b : Axis) :
    (angularCoordinateRicci a b + -angularFormulaRicci a b).num = [] := by
  fin_cases a <;> fin_cases b
  · exact entry_tt_checked
  · exact entry_tr_checked
  · exact entry_tv_checked
  · exact entry_tq_checked
  · exact entry_rt_checked
  · exact entry_rr_checked
  · exact entry_rv_checked
  · exact entry_rq_checked
  · exact entry_vt_checked
  · exact entry_vr_checked
  · exact entry_vv_checked
  · exact entry_vq_checked
  · exact entry_qt_checked
  · exact entry_qr_checked
  · exact entry_qv_checked
  · exact entry_qq_checked

section Evaluation

variable (r w m c : K) (T P : RadialJet K) (E : Mixed.PolarParentJets K)
variable (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0)

local notation "x" => angleValues r w m c T P (Mixed.extraValues E)
local notation "v" => (Fraction.eval x)
local notation "ev" => angularEvaluation x hr hh hs
local notation "C" => modeEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2)) E T P
local notation "F" => chartSourceTensor m c C

private theorem inverse_radius_value : v (rInv 1) = 1/r := by
  simp [rInv, Denominator.eval, angleValues]

private theorem inverse_horizon_value : v (hInv 1) = 1/(r-2) := by
  simp [hInv, Denominator.eval, angleValues]

include hr hh hs

private theorem evaluate_chart_metric (a b : Axis) :
    v ((affineBackground angularCosine a b).value) = metricValues r c a b :=
  congrArg (fun M : SecondMetric K => (M a b).value)
    (Vacuum.chart_metric r w m c T P E hr hh hs)

private theorem evaluate_coordinate_ricci (a b : Axis) :
    v (angularCoordinateRicci a b) =
      Vacuum.linearJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c)
        (reggeWheelerChartMetric w m c T P E) a b := by
  have H : Evaluation.secondMatrix ev (combinedChartInput angularCosine) =
      reggeWheelerChartMetric w m c T P E := by
    funext i j
    have polar : Evaluation.second ev (Mixed.polarParent angularCosine i j) =
        Mixed.polarMetric w m c E i j := by
      simpa only [angularCosine, Fraction.eval_indeterminate, angleValues] using
        Mixed.map_polar r w m c T P E hr hh hs angularCosine i j
    have axial : Evaluation.second ev (affineParent angularCosine i j) =
        fullAngleParentMetric w m c T P i j := by
      simpa only [angularCosine, Fraction.eval_indeterminate, angleValues] using
        PureOdd.map_parent r w m c T P (Mixed.extraValues E) hr hh hs angularCosine i j
    have add_jet (h j : SecondJet Fraction) :
        Evaluation.second ev (Mixed.addJets h j) =
          (Evaluation.second ev h).add (Evaluation.second ev j) := by
      simp [Mixed.addJets, Evaluation.second, SecondJet.add, Fraction.eval_add x hr hh hs]
    simp only [Evaluation.secondMatrix, combinedChartInput, add_jet, polar, axial, reggeWheelerChartMetric]
  change Evaluation.value ev (Vacuum.parentRicci (Fraction.constant (1/2))
    (affineBackground angularCosine) (affineInverse angularCosine angularInverseSine)
      (combinedChartInput angularCosine) a b) = _
  have background : Evaluation.secondMatrix ev (affineBackground angularCosine) =
      fullAngleBackground r c :=
    Vacuum.chart_metric r w m c T P E hr hh hs
  have inverse : jetDiagonal (fun i => Evaluation.first ev (affineInverse angularCosine angularInverseSine i)) =
      fullAngleBackgroundInverse r c :=
    Vacuum.chart_inverse r w m c T P E hr hh hs
  rw [Vacuum.parent_ricci_value ev _ (Vacuum.chart_half r w m c T P E hr hh hs),
    background, inverse, H]

set_option maxHeartbeats 400000 in
private theorem evaluate_formula (a b : Axis) :
    v (angularFormulaTensor a b) = F a b := by
  fin_cases a <;> fin_cases b <;>
    simp only [angularFormulaTensor, modeCoefficientData, chartSourceTensor, Matrix.of_apply,
      modeTensor, modeEinstein, polarEinstein, axialEinstein,
      angularCosine, polarInputs, axialTimeInput, axialRadiusInput, Fraction.eval_add x hr hh hs,
      Fraction.eval_mul, Fraction.eval_neg, Fraction.eval_constant, Fraction.eval_indeterminate,
      inverse_radius_value, inverse_horizon_value, angleValues, Mixed.extraValues, Rat.cast_one]

private theorem evaluate_formula_ricci (a b : Axis) :
    v (angularFormulaRicci a b) = einstein (1/2) (metricValues r c) (inverseValues r c) F a b := by
  have tr : v (modeTrace Fraction.constant (Fraction.indeterminate 0) (rInv 1) (hInv 1) modeCoefficientData) =
      modeTrace (fun q => (q : K)) r (1/r) (1/(r-2)) C := by
    simp only [modeTrace, modeCoefficientData, modeEinstein, polarEinstein, polarInputs,
      Fraction.eval_add x hr hh hs, Fraction.eval_mul, Fraction.eval_neg, Fraction.eval_constant,
      Fraction.eval_indeterminate, inverse_radius_value, inverse_horizon_value, angleValues, Mixed.extraValues]
  unfold einstein
  rw [harmonic_trace r m c C hr hs]
  simp only [angularFormulaRicci, Fraction.eval_add x hr hh hs,
    Fraction.eval_mul, Fraction.eval_neg, Fraction.eval_constant, evaluate_formula r w m c T P E hr hh hs,
    evaluate_chart_metric r w m c T P E hr hh hs, tr, sub_eq_add_neg]
  norm_num
  ring

theorem full_angle_einstein_of_mode :
    linearChartEinstein r c (reggeWheelerChartMetric w m c T P E) = F := by
  have H : Vacuum.linearJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c)
        (reggeWheelerChartMetric w m c T P E) =
      einstein (1/2) (metricValues r c) (inverseValues r c) F := by
    funext a b
    have eq := Fraction.eq_of_zero_numerator x hr hh hs _ _ (coordinate_ricci_certificate a b)
    rw [evaluate_coordinate_ricci r w m c T P E hr hh hs,
      evaluate_formula_ricci r w m c T P E hr hh hs] at eq
    exact eq
  unfold linearChartEinstein
  rw [H]
  exact trace_reversal_twice r c F hr hh hs

end Evaluation

#print axioms full_angle_einstein_of_mode

end
end SchwarzschildEinstein.PureOdd.Master
