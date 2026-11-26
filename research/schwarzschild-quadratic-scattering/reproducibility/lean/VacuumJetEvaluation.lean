import VacuumAngularData
import VacuumJetGeometry
import MixedAngularInput

/-! Transport the finite background and first-order calculations to a
field at a regular point of the manuscript's angular chart. -/
namespace SchwarzschildEinstein.PureOdd.Vacuum

open scoped BigOperators
open AngularCalculation AngularArithmetic

noncomputable section
variable {K S : Type*} [Field K] [Zero S] [Add S] [Neg S] [Mul S]

section Transport

variable (e : Evaluation S K) (half : S) (hhalf : e.value half = 1/2)

private def connectionValue (G : Connection Axis (FirstJet S)) : Connection Axis (FirstJet K) :=
  fun a b c => e.first (G a b c)

private theorem map_axis_derivative (u : SecondJet S) (i : Axis) :
    e.first (AngularCalculation.derivative u i) = (e.second u).derivative i := rfl

private theorem map_derivative (g : SecondMetric S) (a b c : Axis) :
    e.first (AngularCalculation.metricDerivative g a b c) = jetMetricDerivative (e.secondMatrix g) a b c := by
  simp only [AngularCalculation.metricDerivative, jetMetricDerivative, FirstJet.sub, Evaluation.secondMatrix,
    Evaluation.first_add, Evaluation.first_neg, map_axis_derivative]

include hhalf in
private theorem map_connection (B : FirstMetric S) (g : SecondMetric S) :
    connectionValue e (AngularCalculation.christoffel half B g) =
      jetChristoffel (e.firstMatrix B) (e.secondMatrix g) := by
  have sum (f : Axis → FirstJet S) :
      e.first (firstSum f) = FirstJet.sum (fun i => e.first (f i)) := by
    simp [Evaluation.first, firstSum, FirstJet.sum]
  funext a b c
  simp [connectionValue, AngularCalculation.christoffel, jetChristoffel,
    Evaluation.firstMatrix, hhalf, sum]

include hhalf in
private theorem map_diag_connection (B : Axis → FirstJet S) (g : SecondMetric S) :
    connectionValue e (christoffelDiag half B g) =
      jetChristoffel (jetDiagonal (fun i => e.first (B i))) (e.secondMatrix g) := by
  funext a b c
  simp only [connectionValue, christoffelDiag, Evaluation.first_mul, Evaluation.first_constant,
    map_derivative, hhalf, jetChristoffel]
  let z := (e.first (B a)).mul (jetMetricDerivative (e.secondMatrix g) a b c)
  have entries (i : Axis) :
      (jetDiagonal (fun i => e.first (B i)) a i).mul (jetMetricDerivative (e.secondMatrix g) i b c) =
        if i = a then z else FirstJet.constant 0 := by
    by_cases hi : i = a
    · subst i
      simp [jetDiagonal, z]
    · simp [jetDiagonal, hi, Ne.symm hi, jet_zero_mul]
  simp only [entries, jet_indicator_sum]
  rfl

private theorem map_inverse_one (B : Axis → FirstJet S) (H : SecondMetric S) :
    e.firstMatrix (matNeg (inverseOne B (fun i j => (H i j).toFirstJet))) =
      let I := jetDiagonal (fun i => e.first (B i))
      jetMatNeg (jetMatMul (jetMatMul I (fun i j => (e.secondMatrix H i j).toFirstJet)) I) := by
  dsimp only
  rw [mul_jetDiagonal, jetDiagonal_mul]
  funext a b
  simp [Evaluation.firstMatrix, Evaluation.secondMatrix, matNeg, inverseOne, jetMatNeg]

private theorem map_jet_product (A B : Connection Axis (FirstJet S)) (a b : Axis) :
    e.value (product A B a b) =
      connectionProduct (values (connectionValue e A)) (values (connectionValue e B)) a b := by
  simp [product, connectionProduct, values, connectionValue, e.add, e.neg, e.mul, sub_eq_add_neg]

private theorem map_jet_divergence (G : Connection Axis (FirstJet S)) (a b : Axis) :
    e.value (divergence G a b) = jetDivergence (connectionValue e G) a b := by
  simp [divergence, jetDivergence, connectionValue, e.add, e.neg, sub_eq_add_neg]

include hhalf in
private theorem map_background (g : SecondMetric S) (B : Axis → FirstJet S) (a b : Axis) :
    e.value (backgroundRicci half g B a b) =
      backgroundJetRicci (e.secondMatrix g) (jetDiagonal (fun i => e.first (B i))) a b := by
  simp only [backgroundRicci, e.add, map_jet_divergence, map_jet_product,
    map_diag_connection e half hhalf, backgroundJetRicci, Matrix.add_apply]

include hhalf in
theorem parent_ricci_value (g : SecondMetric S) (B : Axis → FirstJet S) (H : SecondMetric S)
    (a b : Axis) :
    e.value (parentRicci half g B H a b) =
      linearJetRicci (e.secondMatrix g) (jetDiagonal (fun i => e.first (B i))) (e.secondMatrix H) a b := by
  have sum (A B : Connection Axis (FirstJet S)) :
      connectionValue e (connectionAdd A B) = jetConnectionAdd (connectionValue e A) (connectionValue e B) := by
    funext a b c
    exact e.first_add _ _
  simp only [parentRicci, e.add, map_jet_divergence, map_jet_product, sum,
    map_connection e half hhalf, map_diag_connection e half hhalf, map_inverse_one,
    linearJetRicci, Matrix.add_apply]

end Transport

section Chart

variable [CharZero K] (r k ell c : K) (T P : RadialJet K) (E : Mixed.PolarParentJets K)
variable (hr : r ≠ 0) (hh : r-2 ≠ 0) (hs : sineSquared c ≠ 0)

local notation "x" => angleValues r k ell c T P (Mixed.extraValues E)
local notation "e" => angularEvaluation x hr hh hs
local notation "C" => (Fraction.indeterminate 1)
local notation "I" => (Fraction.inverse ⟨0, 0, 1⟩)
local notation "Q" => (Fraction.constant (1/2))

include hr hh hs

theorem chart_metric :
    Evaluation.secondMatrix e (affineBackground C) = fullAngleBackground r c := by
  funext a b
  simpa [Evaluation.secondMatrix, angleValues] using
    PureOdd.map_background r k ell c T P (Mixed.extraValues E) hr hh hs C a b

theorem chart_inverse :
    jetDiagonal (fun i => Evaluation.first e (affineInverse C I i)) = fullAngleBackgroundInverse r c := by
  have hI : Fraction.eval x I = 1/sineSquared (Fraction.eval x C) := by
    simp [Denominator.eval, angleValues]
  unfold fullAngleBackgroundInverse
  congr 1
  funext a
  simpa [angleValues] using map_inverse r k ell c T P (Mixed.extraValues E) hr hh hs C I hI a

theorem chart_half : Evaluation.value e Q = 1/2 := by
  change Fraction.eval x Q = _
  norm_num

theorem evaluate_background (a b : Axis) :
    (backgroundAt a b).eval x = backgroundJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c) a b := by
  change Evaluation.value e (backgroundRicci Q (affineBackground C) (affineInverse C I) a b) = _
  rw [map_background e Q (chart_half r k ell c T P E hr hh hs),
    chart_metric r k ell c T P E hr hh hs, chart_inverse r k ell c T P E hr hh hs]

theorem evaluate_even (a b : Axis) :
    (evenAt a b).eval x = linearJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c)
      (Mixed.polarMetric k ell c E) a b := by
  have H : Evaluation.secondMatrix e (Mixed.polarParent C) = Mixed.polarMetric k ell c E := by
    funext a b
    simpa [Evaluation.secondMatrix, angleValues] using Mixed.map_polar r k ell c T P E hr hh hs C a b
  change Evaluation.value e (parentRicci Q (affineBackground C) (affineInverse C I) (Mixed.polarParent C) a b) = _
  rw [parent_ricci_value e Q (chart_half r k ell c T P E hr hh hs), H,
    chart_metric r k ell c T P E hr hh hs, chart_inverse r k ell c T P E hr hh hs]

theorem evaluate_odd (a b : Axis) :
    (oddAt a b).eval x = linearJetRicci (fullAngleBackground r c) (fullAngleBackgroundInverse r c)
      (fullAngleParentMetric k ell c T P) a b := by
  have H : Evaluation.secondMatrix e (affineParent C) = fullAngleParentMetric k ell c T P := by
    funext a b
    simpa [Evaluation.secondMatrix, angleValues] using
      PureOdd.map_parent r k ell c T P (Mixed.extraValues E) hr hh hs C a b
  change Evaluation.value e (parentRicci Q (affineBackground C) (affineInverse C I) (affineParent C) a b) = _
  rw [parent_ricci_value e Q (chart_half r k ell c T P E hr hh hs), H,
    chart_metric r k ell c T P E hr hh hs, chart_inverse r k ell c T P E hr hh hs]

#print axioms evaluate_background
#print axioms evaluate_even
#print axioms evaluate_odd

end Chart
end
end SchwarzschildEinstein.PureOdd.Vacuum
