import EinsteinExpansion
import CoordinateJetTypes
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp


/-! Values and first two coordinate derivatives used in the coordinate
Einstein calculation. Keep the derivative order explicit so a chart can
be evaluated after taking its angular derivatives. -/
namespace SchwarzschildEinstein

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace FirstJet

def constant (x : K) : FirstJet K := ⟨x, fun _ => 0⟩
def add (x y : FirstJet K) : FirstJet K :=
  ⟨x.value + y.value, fun i => x.gradient i + y.gradient i⟩
def neg (x : FirstJet K) : FirstJet K := ⟨-x.value, fun i => -x.gradient i⟩
def sub (x y : FirstJet K) : FirstJet K := add x (neg y)
def mul (x y : FirstJet K) : FirstJet K :=
  ⟨x.value*y.value, fun i => x.gradient i*y.value+x.value*y.gradient i⟩
def sum (x : Axis → FirstJet K) : FirstJet K :=
  ⟨∑ i, (x i).value, fun a => ∑ i, (x i).gradient a⟩

variable [Algebra ℚ K] (d : Axis → Derivation ℚ K K)

def of (x : K) : FirstJet K := ⟨x, fun a => d a x⟩

@[simp] theorem of_constant (a : ℚ) :
    of d (algebraMap ℚ K a) = constant (algebraMap ℚ K a) := by
  unfold of constant
  congr 1
  funext i
  exact (d i).map_algebraMap a

@[simp] theorem of_add (x y : K) : of d (x+y) = add (of d x) (of d y) := by
  simp [of, add, map_add]

@[simp] theorem of_neg (x : K) : of d (-x) = neg (of d x) := by
  simp [of, neg, map_neg]

@[simp] theorem of_sub (x y : K) : of d (x-y) = sub (of d x) (of d y) := by
  simp [of, add, neg, sub, sub_eq_add_neg]

@[simp] theorem of_mul (x y : K) : of d (x*y) = mul (of d x) (of d y) := by
  simp only [of, mul, Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]

@[simp] theorem of_sum (f : Axis → K) : of d (∑ a, f a) = sum (fun a => of d (f a)) := by
  simp [of, sum, map_sum]

end FirstJet

namespace SecondJet

def constant (x : K) : SecondJet K := ⟨FirstJet.constant x, fun _ _ => 0⟩
def mul (x y : SecondJet K) : SecondJet K :=
  ⟨FirstJet.mul x.toFirstJet y.toFirstJet,
   fun i j => x.second i j*y.value+x.gradient j*y.gradient i+
     x.gradient i*y.gradient j+x.value*y.second i j⟩
def neg (x : SecondJet K) : SecondJet K :=
  ⟨FirstJet.neg x.toFirstJet, fun i j => -x.second i j⟩
def add (x y : SecondJet K) : SecondJet K :=
  ⟨FirstJet.add x.toFirstJet y.toFirstJet, fun i j => x.second i j+y.second i j⟩
def sub (x y : SecondJet K) : SecondJet K := add x (neg y)
def inv (x : SecondJet K) : SecondJet K :=
  ⟨⟨x.value⁻¹, fun i => -x.gradient i/x.value^2⟩,
    fun i j => 2*x.gradient i*x.gradient j/x.value^3-x.second i j/x.value^2⟩
def divide (x y : SecondJet K) : SecondJet K := mul x (inv y)
def derivative (x : SecondJet K) (j : Axis) : FirstJet K :=
  ⟨x.gradient j, fun i => x.second i j⟩

variable [Algebra ℚ K] (d : Axis → Derivation ℚ K K)

def of (x : K) : SecondJet K := ⟨FirstJet.of d x, fun i j => d i (d j x)⟩

@[simp] theorem of_constant (a : ℚ) :
    of d (algebraMap ℚ K a) = constant (algebraMap ℚ K a) := by
  unfold of constant
  rw [FirstJet.of_constant]
  congr 1
  funext i j
  rw [(d j).map_algebraMap, map_zero]

@[simp] theorem of_neg (x : K) : of d (-x) = neg (of d x) := by
  simp [of, neg, map_neg]

@[simp] theorem of_add (x y : K) : of d (x+y) = add (of d x) (of d y) := by
  simp [of, add, map_add]

@[simp] theorem of_sub (x y : K) : of d (x-y) = sub (of d x) (of d y) := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem of_mul (x y : K) : of d (x*y) = mul (of d x) (of d y) := by
  unfold of mul
  rw [FirstJet.of_mul]
  congr 1
  funext i j
  simp only [Derivation.leibniz, smul_eq_mul, map_add, FirstJet.of]
  ring

theorem of_inv (x : K) (hx : x ≠ 0) : of d x⁻¹ = inv (of d x) := by
  unfold of inv FirstJet.of
  congr 1
  · congr 1
    funext i
    rw [(d i).leibniz_inv, smul_eq_mul]
    field_simp [hx]
  · funext i j
    simp only [Derivation.leibniz_inv, pow_two, smul_eq_mul, map_neg, Derivation.leibniz]
    field_simp [hx]
    ring

theorem of_divide (x y : K) (hy : y ≠ 0) : of d (x/y) = divide (of d x) (of d y) := by
  rw [div_eq_mul_inv, of_mul, of_inv d y hy]
  rfl

@[simp] theorem derivative_of (x : K) (j : Axis) :
    derivative (of d x) j = FirstJet.of d (d j x) := rfl

end SecondJet

def jetMatMul (A B : FirstMetric K) : FirstMetric K :=
  fun i j => FirstJet.sum fun a => FirstJet.mul (A i a) (B a j)

def jetMatNeg (A : FirstMetric K) : FirstMetric K := fun i j => FirstJet.neg (A i j)

def jetMetricDerivative (g : SecondMetric K) (a b c : Axis) : FirstJet K :=
  FirstJet.sub
    (FirstJet.add ((g a c).derivative b) ((g a b).derivative c)) ((g b c).derivative a)

def jetChristoffel (B : FirstMetric K) (g : SecondMetric K) : Connection Axis (FirstJet K) :=
  fun a b c => FirstJet.mul (FirstJet.constant (1/2))
    (FirstJet.sum fun j => FirstJet.mul (B a j) (jetMetricDerivative g j b c))

def jetConnectionAdd (a b : Connection Axis (FirstJet K)) : Connection Axis (FirstJet K) :=
  fun i j k => FirstJet.add (a i j k) (b i j k)

def values (Γ : Connection Axis (FirstJet K)) : Connection Axis K :=
  fun a b c => (Γ a b c).value

def quadraticJetRicciOfInverse (g H : SecondMetric K) (B B1 B2 : FirstMetric K) :
    Tensor Axis K :=
  let G0 := jetChristoffel B g
  let G1 := jetConnectionAdd (jetChristoffel B H) (jetChristoffel B1 g)
  let G2 := jetConnectionAdd (jetChristoffel B1 H) (jetChristoffel B2 g)
  let div : Tensor Axis K := fun a b => ∑ c, ((G2 c a b).gradient c - (G2 c a c).gradient b)
  div + (connectionProduct (values G0) (values G2) +
    connectionProduct (values G1) (values G1) + connectionProduct (values G2) (values G0))

def quadraticJetRicci (g : SecondMetric K) (B : FirstMetric K) (H : SecondMetric K) :
    Tensor Axis K :=
  let h : FirstMetric K := fun a b => (H a b).toFirstJet
  let BhB := jetMatMul (jetMatMul B h) B
  let BhBhB := jetMatMul (jetMatMul BhB h) B
  quadraticJetRicciOfInverse g H B (jetMatNeg BhB) BhBhB

def jetDiagonal (b : Axis → FirstJet K) : FirstMetric K :=
  fun a j => if a = j then b a else FirstJet.constant 0

private theorem jet_mul_zero (x : FirstJet K) : FirstJet.mul x (FirstJet.constant 0) =
    FirstJet.constant 0 := by
  simp [FirstJet.mul, FirstJet.constant]

theorem jet_zero_mul (x : FirstJet K) : FirstJet.mul (FirstJet.constant 0) x =
    FirstJet.constant 0 := by
  simp [FirstJet.mul, FirstJet.constant]

theorem jet_indicator_sum (q : Axis) (x : FirstJet K) :
    FirstJet.sum (fun i => if i = q then x else FirstJet.constant 0) = x := by
  rcases x with ⟨val, grad⟩
  simp [FirstJet.sum, FirstJet.constant, apply_ite]
  funext a
  have part (i : Axis) :
      (if i = q then (⟨val, grad⟩ : FirstJet K) else ⟨0, fun _ => 0⟩).gradient a =
        if i = q then grad a else 0 := by
    split <;> rfl
  simp [part]

theorem jetDiagonal_mul (b : Axis → FirstJet K) (H : FirstMetric K) :
    jetMatMul (jetDiagonal b) H = fun a j => FirstJet.mul (b a) (H a j) := by
  funext a j
  unfold jetMatMul jetDiagonal
  have entries : (fun i => FirstJet.mul (if a = i then b a else FirstJet.constant 0) (H i j)) =
      (fun i => if i = a then FirstJet.mul (b a) (H a j) else FirstJet.constant 0) := by
    funext i
    by_cases eq : i = a
    · simp [eq]
    · simp [eq, Ne.symm eq, jet_zero_mul]
  rw [entries, jet_indicator_sum]

theorem mul_jetDiagonal (b : Axis → FirstJet K) (H : FirstMetric K) :
    jetMatMul H (jetDiagonal b) = fun a j => FirstJet.mul (H a j) (b j) := by
  funext a j
  unfold jetMatMul jetDiagonal
  have entries : (fun i => FirstJet.mul (H a i) (if i = j then b i else FirstJet.constant 0)) =
      (fun i => if i = j then FirstJet.mul (H a j) (b j) else FirstJet.constant 0) := by
    funext i
    by_cases eq : i = j <;> simp [eq, jet_mul_zero]
  rw [entries, jet_indicator_sum]

variable [Algebra ℚ K] (d : Axis → Derivation ℚ K K)

def firstMetric (g : Tensor Axis K) : FirstMetric K := fun a b => FirstJet.of d (g a b)
def secondMetric (g : Tensor Axis K) : SecondMetric K := fun a b => SecondJet.of d (g a b)

private theorem jetMatMul_correct (g h : Tensor Axis K) :
    jetMatMul (firstMetric d g) (firstMetric d h) = firstMetric d (g*h) := by
  funext i j
  simp [jetMatMul, firstMetric, Matrix.mul_apply]

private theorem jetMatNeg_correct (g : Tensor Axis K) :
    jetMatNeg (firstMetric d g) = firstMetric d (-g) := by
  funext i j
  simp [jetMatNeg, firstMetric]

private theorem jetChristoffel_correct (B g : Tensor Axis K) :
    jetChristoffel (firstMetric d B) (secondMetric d g) =
      fun a b c => FirstJet.of d (christoffel (1/2) (fun a => d a) B g a b c) := by
  funext a b c
  have half : FirstJet.of d (2⁻¹ : K) = FirstJet.constant 2⁻¹ := by
    simpa using FirstJet.of_constant d (1/2)
  simp [jetChristoffel, firstMetric, secondMetric, christoffel, jetMetricDerivative,
    metricDerivative, half]

/-- The finite jet computation is the quadratic Ricci tensor, with
coordinates differentiated before evaluation. -/
theorem quadratic_ricci_from_jets (g B H : Tensor Axis K) :
    quadraticJetRicci (secondMetric d g) (firstMetric d B) (secondMetric d H) =
      quadraticRicci (fun a => d a) g B H := by
  have first : (fun a b => (secondMetric d H a b).toFirstJet) = firstMetric d H := rfl
  unfold quadraticJetRicci quadraticJetRicciOfInverse quadraticRicci
  simp only [first, jetMatMul_correct, jetMatNeg_correct, jetChristoffel_correct]
  ext a b
  simp only [Matrix.add_apply, connectionDivergence, quadraticConnection, linearConnection,
    jetConnectionAdd, FirstJet.of, FirstJet.add, Pi.add_apply, map_add]
  rfl

#print axioms quadratic_ricci_from_jets

end
end SchwarzschildEinstein
