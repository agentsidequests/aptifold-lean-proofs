import MixedRadialFormulas
import PureOddRowCalculus

/-! Interpret the radial coefficient rows on a common parent J. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (d : Derivation ℚ K K)

private theorem linear_value_add (J Z : K) (a b : Linear K) :
    linearValue J Z (linearAdd a b) = linearValue J Z a+linearValue J Z b := by
  simp only [linearValue, linearAdd]
  ring

private theorem linear_value_scale (J Z s : K) (a : Linear K) :
    linearValue J Z (linearScale s a) = s*linearValue J Z a := by
  simp only [linearValue, linearScale]
  ring

omit [CharZero K] [Algebra ℚ K] in
theorem row_value_add (J Z : K) (a b : Quadratic K) :
    quadraticValue J Z (plus a b) = quadraticValue J Z a+quadraticValue J Z b := by
  simp only [quadraticValue, plus]
  ring

omit [CharZero K] [Algebra ℚ K] in
theorem row_value_scale (J Z s : K) (a : Quadratic K) :
    quadraticValue J Z (scale s a) = s*quadraticValue J Z a := by
  simp only [quadraticValue, scale, mapRow]
  ring

def referenceEven (r k ell J Z : K) : K :=
  (parentSuperpotential r ell*J+Z/r^2)/(parentAlgebraicFrequency ell+k)

theorem polar_reconstruction_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z) :
    mapPolarJets (linearValue J Z) (polarReconstruction d r k ell) =
      scalarPolarReconstruction d r k ell (referenceEven r k ell J Z) := by
  have evenEq : linearValue J Z (evenParentAmplitude r k ell) = referenceEven r k ell J Z := by
    have unit : @OfNat.ofNat K 1 (instOfNat_mixedRadialFormulas 1) = (1 : K) := Nat.cast_one
    simp only [linearValue, evenParentAmplitude, referenceEven, unit]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, ← div_div, ← add_div]
  simp only [mapPolarJets, polarReconstruction, parent_jet_value d r k ell J Z hJ hZ,
    linear_value_add, linear_value_scale, linear_derivative_value d r k ell J Z hJ hZ, evenEq,
    scalarPolarReconstruction, radialJet]

omit [Algebra ℚ K] in
theorem vector_interpolation (r k ell J Z : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) (c : Rat → K) :
    let rows := interpolateVector c r k ell T P E
    let value := vectorSamples c r k ell T P E J Z
    quadraticValue J Z rows.time = value.time ∧ quadraticValue J Z rows.radius = value.radius := by
  dsimp only [interpolateVector, vectorSamples, evaluateVector, recoverRow, vectorCoefficients, mapJet,
    mapPolarJets, quadraticValue]
  constructor <;> ring

theorem bare_mixed_rows_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z) :
    let C : Rat → K := fun q => (q : K)
    let v := vectorSamples C r k ell (parentJet d r k ell (timeAmplitude r))
      (parentJet d r k ell (radiusAmplitude r k)) (polarReconstruction d r k ell) J Z
    quadraticValue J Z (bareMixedRows C d r k ell) = mixedMaster d r k ell v := by
  obtain ⟨ht, hp⟩ := vector_interpolation r k ell J Z
    (parentJet d r k ell (timeAmplitude r)) (parentJet d r k ell (radiusAmplitude r k))
    (polarReconstruction d r k ell) (fun q => (q : K))
  simp only [bareMixedRows, reconstructedVector, mixedMaster, row_value_scale, row_value_add,
    row_derivative_value d r k ell J Z hJ hZ, ht, hp]

#print axioms polar_reconstruction_value
#print axioms bare_mixed_rows_value

end
end SchwarzschildEinstein.PureOdd.Mixed
