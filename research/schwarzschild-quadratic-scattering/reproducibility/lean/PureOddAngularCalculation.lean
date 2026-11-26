import PureOddAngularArithmetic
import PureOddRadialConnection

/-! A four-coordinate evaluation of the jet calculation that can also
run over sparse symbolic fractions. The transport theorems connect the
calculation to the existing coordinate Ricci and Einstein tensors. -/
namespace SchwarzschildEinstein.PureOdd.AngularCalculation

open scoped BigOperators
open AngularArithmetic

variable {S K : Type*} [Zero S] [Add S] [Neg S] [Mul S] [Field K]

structure Evaluation (S K : Type*) [Zero S] [Add S] [Neg S] [Mul S] [Field K] where
  value : S → K
  zero : value 0 = 0
  add (a b : S) : value (a+b) = value a+value b
  neg (a : S) : value (-a) = -value a
  mul (a b : S) : value (a*b) = value a*value b

namespace Evaluation

noncomputable section

variable (e : Evaluation S K)

def first (u : FirstJet S) : FirstJet K := ⟨e.value u.value, fun i => e.value (u.gradient i)⟩
def second (u : SecondJet S) : SecondJet K :=
  ⟨e.first u.toFirstJet, fun i j => e.value (u.second i j)⟩

@[simp] theorem sum_map (f : Axis → S) :
    e.value (sumFour f) = ∑ i, e.value (f i) := by
  simp only [sumFour, sum_axes, e.add]

@[simp] theorem first_constant (a : S) : e.first (firstConstant a) = FirstJet.constant (e.value a) := by
  simp [first, firstConstant, FirstJet.constant, e.zero]

@[simp] theorem first_add (u v : FirstJet S) : e.first (firstAdd u v) = (e.first u).add (e.first v) := by
  simp [first, firstAdd, FirstJet.add, e.add]

@[simp] theorem first_neg (u : FirstJet S) : e.first (firstNeg u) = (e.first u).neg := by
  simp [first, firstNeg, FirstJet.neg, e.neg]

@[simp] theorem first_mul (u v : FirstJet S) : e.first (firstMul u v) = (e.first u).mul (e.first v) := by
  simp [first, firstMul, FirstJet.mul, e.add, e.mul]

@[simp] theorem second_neg (u : SecondJet S) : e.second (secondNeg u) = (e.second u).neg := by
  simp [second, secondNeg, SecondJet.neg, e.neg]

@[simp] theorem second_mul (u v : SecondJet S) :
    e.second (secondMul u v) = (e.second u).mul (e.second v) := by
  simp [second, secondMul, SecondJet.mul, first, firstMul, FirstJet.mul, e.add, e.mul]

@[simp] theorem axis_map (i : Axis) (a b c : S) :
    e.second (axisJet i a b c) = oneAxis i (e.value a) (e.value b) (e.value c) := by
  simp [second, first, axisJet, oneAxis, apply_ite, e.zero]

@[simp] private theorem first_sum (f : Axis → FirstJet S) :
    e.first (firstSum f) = FirstJet.sum (fun i => e.first (f i)) := by
  simp [first, firstSum, FirstJet.sum]

@[simp] private theorem derivative_map (u : SecondJet S) (i : Axis) :
    e.first (derivative u i) = (e.second u).derivative i := rfl

@[simp] theorem value_first (u : FirstJet S) : (e.first u).value = e.value u.value := rfl
@[simp] theorem grad_first (u : FirstJet S) (i : Axis) : (e.first u).gradient i = e.value (u.gradient i) := rfl
@[simp] theorem value_second (u : SecondJet S) : (e.second u).value = e.value u.value := rfl
@[simp] theorem to_first (u : SecondJet S) : (e.second u).toFirstJet = e.first u.toFirstJet := rfl

def firstMatrix (B : FirstMetric S) : FirstMetric K := fun i j => e.first (B i j)
def secondMatrix (g : SecondMetric S) : SecondMetric K := fun i j => e.second (g i j)
private def conn (G : Connection Axis (FirstJet S)) : Connection Axis (FirstJet K) :=
  fun i j k => e.first (G i j k)

private theorem inverse_one_map (B : Axis → FirstJet S) (J : FirstMetric S) :
    e.firstMatrix (inverseOne B J) =
      jetMatMul (jetMatMul (jetDiagonal (fun i => e.first (B i))) (e.firstMatrix J))
        (jetDiagonal (fun i => e.first (B i))) := by
  rw [mul_jetDiagonal, jetDiagonal_mul]
  funext a b
  simp [firstMatrix, inverseOne]

private theorem inverse_two_map (B : Axis → FirstJet S) (J : FirstMetric S) :
    e.firstMatrix (inverseTwo B J) =
      let d := jetDiagonal (fun i => e.first (B i))
      jetMatMul (jetMatMul (jetMatMul (jetMatMul d (e.firstMatrix J)) d)
        (e.firstMatrix J)) d := by
  dsimp only
  rw [mul_jetDiagonal, ← e.inverse_one_map]
  funext a b
  simp [firstMatrix, inverseTwo, jetMatMul]

private theorem mat_neg (B : FirstMetric S) :
    e.firstMatrix (matNeg B) = jetMatNeg (e.firstMatrix B) := by
  funext a b
  exact e.first_neg _

@[simp] private theorem metric_derivative_map (g : SecondMetric S) (a b c : Axis) :
    e.first (metricDerivative g a b c) = jetMetricDerivative (e.secondMatrix g) a b c := by
  simp [metricDerivative, jetMetricDerivative, FirstJet.sub, secondMatrix]

private theorem christoffel_map (half : S) (B : FirstMetric S) (g : SecondMetric S)
    (h : e.value half = 1/2) :
    e.conn (christoffel half B g) = jetChristoffel (e.firstMatrix B) (e.secondMatrix g) := by
  funext a b c
  simp [conn, firstMatrix, christoffel, jetChristoffel, h]

private theorem christoffel_diag_map (half : S) (B : Axis → FirstJet S) (g : SecondMetric S)
    (h : e.value half = 1/2) :
    e.conn (christoffelDiag half B g) =
      jetChristoffel (jetDiagonal (fun i => e.first (B i))) (e.secondMatrix g) := by
  funext a b c
  simp only [conn, christoffelDiag, e.first_mul, e.first_constant, e.metric_derivative_map, h,
    jetChristoffel]
  let z := (e.first (B a)).mul (jetMetricDerivative (e.secondMatrix g) a b c)
  have entries (i : Axis) :
      (jetDiagonal (fun i => e.first (B i)) a i).mul (jetMetricDerivative (e.secondMatrix g) i b c) =
        if i = a then z else FirstJet.constant 0 := by
    by_cases hi : i = a
    · subst i
      simp [jetDiagonal, z]
    · simp [jetDiagonal, hi, Ne.symm hi, jet_zero_mul]
  simp only [entries, jet_indicator_sum] <;> rfl

private theorem connection_add (A B : Connection Axis (FirstJet S)) :
    e.conn (connectionAdd A B) = jetConnectionAdd (e.conn A) (e.conn B) := by
  funext a b c
  exact e.first_add _ _

private theorem product_map (A B : Connection Axis (FirstJet S)) (a b : Axis) :
    e.value (product A B a b) =
      connectionProduct (values (e.conn A)) (values (e.conn B)) a b := by
  simp [product, connectionProduct, values, conn, e.add, e.neg, e.mul, sub_eq_add_neg]

private theorem divergence_map (G : Connection Axis (FirstJet S)) (a b : Axis) :
    e.value (divergence G a b) =
      ∑ i, ((e.conn G i a b).gradient i-(e.conn G i a i).gradient b) := by
  simp [divergence, conn, e.add, e.neg, sub_eq_add_neg]

theorem ricci_map (half : S) (g : SecondMetric S) (B : Axis → FirstJet S) (H : SecondMetric S)
    (a b : Axis) (h : e.value half = 1/2) :
    e.value (ricci half g B H a b) =
      quadraticJetRicci (e.secondMatrix g) (jetDiagonal (fun i => e.first (B i)))
        (e.secondMatrix H) a b := by
  have mapGamma (A : FirstMetric S) (m : SecondMetric S) := e.christoffel_map half A m h
  have mapDiagonal (m : SecondMetric S) := e.christoffel_diag_map half B m h
  change e.value (ricci half g B H a b) = _
  unfold ricci
  dsimp only
  simp only [ricciParts, e.add, if_pos rfl, show (1:Axis) ≠ 0 from by decide,
    show (2:Axis) ≠ 0 from by decide, show (3:Axis) ≠ 0 from by decide,
    show (2:Axis) ≠ 1 from by decide, show (3:Axis) ≠ 1 from by decide, show (3:Axis) ≠ 2 from by decide,
    if_neg, if_true, if_false, e.divergence_map, e.product_map, e.connection_add,
    mapGamma, mapDiagonal, e.mat_neg]
  rw [e.inverse_one_map B (fun i j => (H i j).toFirstJet),
    e.inverse_two_map B (fun i j => (H i j).toFirstJet)]
  rfl

end
end Evaluation

end SchwarzschildEinstein.PureOdd.AngularCalculation
