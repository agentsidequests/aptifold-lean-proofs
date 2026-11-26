import ParityMasterReadoutsChecks
import VacuumJetEvaluation

/-! Identify the verified scalar readouts with the trace-reversed
linearized coordinate tensor of the two Regge–Wheeler gauge metrics. -/
namespace SchwarzschildEinstein.PureOdd.Master

open AngularArithmetic AngularCalculation
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

def equatorialEinstein (r : K) (H : SecondMetric K) : Tensor Axis K :=
  let g := fullAngleBackground r 0
  let B := fullAngleBackgroundInverse r 0
  einstein (1/2) (fun a b => (g a b).value) (fun a b => (B a b).value)
    (Vacuum.linearJetRicci g B H)

def reggeWheelerGaugeMetric (w m : K) (T P : RadialJet K) (E : Mixed.PolarParentJets K) : SecondMetric K :=
  fun a b => (Mixed.polarMetric w m 0 E a b).add (fullAngleParentMetric w m 0 T P a b)

private def undividedPolar (G : Tensor Axis K) : EvenSource K :=
  ⟨G 0 0,G 1 1,G 1 3,(G 2 2-G 3 3)/2,G 2 2+G 3 3⟩

private def weightedPolar (m : K) (s : EvenSource K) : EvenSource K :=
  ⟨s.tt,s.rr,m*s.radialVector,s.sphereTrace,m*(m-1)*s.traceFree⟩

private def normalizePolar (m : K) (s : EvenSource K) : EvenSource K :=
  ⟨s.tt,s.rr,s.radialVector/m,s.sphereTrace,s.traceFree/(m*(m-1))⟩

def polarSourceReadout (m : K) (G : Tensor Axis K) : EvenSource K :=
  normalizePolar m (undividedPolar G)

def axialSourceReadout (m : K) (G : Tensor Axis K) : Mixed.AxialVector K :=
  ⟨-(G 0 2/m),-(G 1 2/m)⟩

private def mapPolarReadouts (v : Fraction → K) (s : EvenSource Fraction) : EvenSource K :=
  ⟨v s.tt,v s.rr,v s.radialVector,v s.sphereTrace,v s.traceFree⟩

private theorem trace_reversal (r : K) (R : Tensor Axis K) :
    let g := fullAngleBackground r 0
    let B := fullAngleBackgroundInverse r 0
    undividedPolar (einstein (1/2) (fun a b => (g a b).value) (fun a b => (B a b).value) R) =
      unnormalizedPolarReadouts (fun q => (q : K)) r (1/r) (1/(r-2)) R := by
  norm_num [undividedPolar, unnormalizedPolarReadouts, einstein, contraction, sum_axes,
    fullAngleBackground, fullAngleBackgroundInverse, fullAngleInverseDiagonal, background,
    inverseDiagonal, jetDiagonal, sineSquared, oneAxis, polar, SecondJet.mul, FirstJet.mul,
    SecondJet.constant, FirstJet.constant, Fin.ext_iff, -Fin.val_eq_zero_iff, div_eq_mul_inv,
    sub_eq_add_neg, pow_two]
  exact ⟨by ring, by ring, by ring, by ring⟩

section Evaluation

variable (r w m : K) (T P : RadialJet K) (E : Mixed.PolarParentJets K)
variable (hr : r ≠ 0) (hh : r-2 ≠ 0)

local notation "X" => Fraction.indeterminate
local notation "Q" => Fraction.constant
local notation "x" => angleValues r w m 0 T P (Mixed.extraValues E)
local notation "v" => (Fraction.eval x)
private theorem equator_sine : sineSquared (x 1) ≠ 0 := by
  norm_num [sineSquared, angleValues]

local notation "hs" => equator_sine r w m T P E
local notation "e" => angularEvaluation x hr hh hs
local notation "g" => (fullAngleBackground r 0)
local notation "B" => (fullAngleBackgroundInverse r 0)

private theorem inverse_radius_value : v (rInv 1) = 1/r := by
  simp [rInv, Denominator.eval, angleValues]

private theorem inverse_horizon_value : v (hInv 1) = 1/(r-2) := by
  simp [hInv, Denominator.eval, angleValues]

include hr hh in
private theorem checked_fraction (a b : Fraction) (h : (a + -b).num = []) :
    v a = v b :=
  Fraction.eq_of_zero_numerator x hr hh hs a b h

include hr hh in
private theorem equatorial_calculation (H : SecondMetric Fraction) (h : SecondMetric K)
    (metric : Evaluation.secondMatrix e H = h) (a b : Axis) :
    v (Vacuum.parentRicci (Q (1/2)) (affineBackground (Q 0)) (affineInverse (Q 0) (Q 1)) H a b) =
      Vacuum.linearJetRicci g B h a b := by
  have half : Evaluation.value e (Q (1/2)) = 1/2 := by
    change v (Q (1/2)) = _
    norm_num
  have bMetric : Evaluation.secondMatrix e (affineBackground (Q 0)) = g := by
    funext i j
    simpa only [Evaluation.secondMatrix, Fraction.eval_constant, Rat.cast_zero] using
      PureOdd.map_background r w m 0 T P (Mixed.extraValues E) hr hh hs (Q 0) i j
  have bInverse : jetDiagonal (fun i => Evaluation.first e (affineInverse (Q 0) (Q 1) i)) = B := by
    have invSine : v (Q 1) = 1/sineSquared (v (Q 0)) := by norm_num [sineSquared]
    unfold fullAngleBackgroundInverse
    congr 1
    funext i
    simpa only [Fraction.eval_constant, Rat.cast_zero] using
      map_inverse r w m 0 T P (Mixed.extraValues E) hr hh hs (Q 0) (Q 1) invSine i
  change Evaluation.value e (Vacuum.parentRicci (Q (1/2)) _ _ H a b) = _
  rw [Vacuum.parent_ricci_value e _ half, bMetric, bInverse, metric]

include hr hh in
private theorem combined_calculation (a b : Axis) :
    v (ricciAtEquator a b) = Vacuum.linearJetRicci g B (reggeWheelerGaugeMetric w m T P E) a b := by
  apply equatorial_calculation r w m T P E hr hh
  funext i j
  have polar : Evaluation.second e (Mixed.polarParent (Q 0) i j) = Mixed.polarMetric w m 0 E i j := by
    simpa only [Fraction.eval_constant, Rat.cast_zero] using Mixed.map_polar r w m 0 T P E hr hh hs (Q 0) i j
  have axial : Evaluation.second e (affineParent (Q 0) i j) = fullAngleParentMetric w m 0 T P i j := by
    simpa only [Fraction.eval_constant, Rat.cast_zero] using
      PureOdd.map_parent r w m 0 T P (Mixed.extraValues E) hr hh hs (Q 0) i j
  have add_jet (h j : SecondJet Fraction) :
      Evaluation.second e (Mixed.addJets h j) =
        (Evaluation.second e h).add (Evaluation.second e j) := by
    simp [Mixed.addJets, Evaluation.second, SecondJet.add, Evaluation.add]
  simp only [Evaluation.secondMatrix, combinedInput, reggeWheelerGaugeMetric, add_jet, polar, axial]

include hr hh in
private theorem polar_readout_transport :
    mapPolarReadouts v polarCoordinateData =
      undividedPolar (equatorialEinstein r (reggeWheelerGaugeMetric w m T P E)) := by
  rw [equatorialEinstein, trace_reversal]
  simp only [mapPolarReadouts, polarCoordinateData, unnormalizedPolarReadouts,
    Fraction.eval_add x hr hh hs, Fraction.eval_mul, Fraction.eval_neg, Fraction.eval_constant,
    Fraction.eval_indeterminate, inverse_radius_value, inverse_horizon_value,
    combined_calculation r w m T P E hr hh, angleValues]

include hr hh in
private theorem polar_formula_transport :
    mapPolarReadouts v polarFormulaData =
      weightedPolar m (polarEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2)) E) := by
  simp only [mapPolarReadouts, polarFormulaData, weightedPolar, polarEinstein, polarInputs,
    Fraction.eval_add x hr hh hs, Fraction.eval_mul, Fraction.eval_neg, Fraction.eval_constant,
    Fraction.eval_indeterminate, angleValues, Mixed.extraValues, inverse_radius_value,
    inverse_horizon_value, Rat.cast_one, sub_eq_add_neg]

include hr hh in
theorem polar_readout_from_tensor (hm : m ≠ 0) (hprev : m-1 ≠ 0) :
    polarSourceReadout m (equatorialEinstein r (reggeWheelerGaugeMetric w m T P E)) =
      polarEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2)) E := by
  have data : mapPolarReadouts v polarCoordinateData = mapPolarReadouts v polarFormulaData := by
    change EvenSource.mk _ _ _ _ _ = EvenSource.mk _ _ _ _ _
    congr 1
    · exact checked_fraction r w m T P E hr hh _ _ polar_time_checked
    · exact checked_fraction r w m T P E hr hh _ _ polar_radius_checked
    · exact checked_fraction r w m T P E hr hh _ _ polar_vector_checked
    · exact checked_fraction r w m T P E hr hh _ _ polar_trace_checked
    · exact checked_fraction r w m T P E hr hh _ _ polar_tracefree_checked
  rw [polar_readout_transport r w m T P E hr hh, polar_formula_transport r w m T P E hr hh] at data
  rw [polarSourceReadout, data]
  simp [normalizePolar, weightedPolar, hm, hprev]

include hr hh in
theorem axial_readout_from_tensor (hm : m ≠ 0) :
    let values := axialEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2)) T P
    axialSourceReadout m (equatorialEinstein r (reggeWheelerGaugeMetric w m T P E)) =
      ⟨-values.time,-values.radius⟩ := by
  have ht := checked_fraction r w m T P E hr hh _ _ axial_time_checked
  have hradius := checked_fraction r w m T P E hr hh _ _ axial_radius_checked
  simp only [axialCoordinateData, axialFormulaData, axialEinstein, axialTimeInput, axialRadiusInput,
    Fraction.eval_add x hr hh hs, Fraction.eval_mul, Fraction.eval_neg, Fraction.eval_constant,
    Fraction.eval_indeterminate, inverse_radius_value, inverse_horizon_value,
    combined_calculation r w m T P E hr hh, angleValues]
    at ht hradius
  simp only [axialSourceReadout, equatorialEinstein, einstein]
  have gtime : (g 0 2).value = 0 := rfl
  have gradius : (g 1 2).value = 0 := rfl
  simp only [gtime, gradius, zero_mul, mul_zero, sub_zero, ht, hradius, axialEinstein]
  simp [hm]

#print axioms polar_readout_from_tensor
#print axioms axial_readout_from_tensor

end Evaluation
end
end SchwarzschildEinstein.PureOdd.Master
