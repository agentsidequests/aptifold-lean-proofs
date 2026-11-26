import CoordinateJets

/-! Coordinate-jet versions of the background Ricci tensor and its first
variation. These compute derivatives before evaluating at the chart point. -/
namespace SchwarzschildEinstein.PureOdd.Vacuum

open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

def jetDivergence (G : Connection Axis (FirstJet K)) : Tensor Axis K :=
  fun a b => ∑ c, ((G c a b).gradient c - (G c a c).gradient b)

def backgroundJetRicci (g : SecondMetric K) (B : FirstMetric K) : Tensor Axis K :=
  let G₀ := jetChristoffel B g
  jetDivergence G₀ + connectionProduct (values G₀) (values G₀)

def linearJetRicci (g : SecondMetric K) (B : FirstMetric K) (H : SecondMetric K) : Tensor Axis K :=
  let h : FirstMetric K := fun a b => (H a b).toFirstJet
  let B₁ := jetMatNeg (jetMatMul (jetMatMul B h) B)
  let G₀ := jetChristoffel B g
  let G₁ := jetConnectionAdd (jetChristoffel B H) (jetChristoffel B₁ g)
  jetDivergence G₁ + (connectionProduct (values G₀) (values G₁) + connectionProduct (values G₁) (values G₀))

variable [Algebra ℚ K] (d : Axis → Derivation ℚ K K)

private theorem christoffel_of_jets (B g : Tensor Axis K) :
    jetChristoffel (firstMetric d B) (secondMetric d g) =
      fun a b c => FirstJet.of d (christoffel (1/2) (fun i => d i) B g a b c) := by
  funext a b c
  have half : FirstJet.of d (2⁻¹ : K) = FirstJet.constant 2⁻¹ := by
    simpa using FirstJet.of_constant d (1/2)
  simp [jetChristoffel, firstMetric, secondMetric, christoffel, jetMetricDerivative,
    metricDerivative, half]

private theorem product_of_jets (B H : Tensor Axis K) :
    jetMatMul (firstMetric d B) (firstMetric d H) = firstMetric d (B*H) := by
  funext a b
  simp [jetMatMul, firstMetric, Matrix.mul_apply]

private theorem negative_of_jets (B : Tensor Axis K) :
    jetMatNeg (firstMetric d B) = firstMetric d (-B) := by
  funext a b
  simp [jetMatNeg, firstMetric]

theorem background_ricci_of_jets (g B : Tensor Axis K) :
    backgroundJetRicci (secondMetric d g) (firstMetric d B) =
      ricci (fun i => d i) (christoffel (1/2) (fun i => d i) B g) := by
  unfold backgroundJetRicci
  rw [christoffel_of_jets]
  rfl

theorem linear_ricci_of_jets (g B H : Tensor Axis K) :
    linearJetRicci (secondMetric d g) (firstMetric d B) (secondMetric d H) =
      linearRicci (fun i => d i) g B H := by
  have h : (fun a b => (secondMetric d H a b).toFirstJet) = firstMetric d H := rfl
  unfold linearJetRicci linearRicci
  simp only [h, product_of_jets, negative_of_jets, christoffel_of_jets]
  ext a b
  simp only [Matrix.add_apply, jetDivergence, connectionDivergence, linearConnection,
    jetConnectionAdd, FirstJet.of, FirstJet.add, Pi.add_apply, map_add]
  rfl

#print axioms background_ricci_of_jets
#print axioms linear_ricci_of_jets

end
end SchwarzschildEinstein.PureOdd.Vacuum
