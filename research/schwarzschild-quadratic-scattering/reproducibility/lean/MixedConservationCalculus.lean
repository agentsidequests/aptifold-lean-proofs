import MixedConservationRows
import MixedRadialCalculus
import MixedSourceReadouts

/-! Evaluate the conservation row on the reconstructed physical parent. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (d : Derivation ℚ K K)

omit [Algebra ℚ K] in
private theorem angular_interpolation (r k ell J Z : K) (T P : RadialJet (Linear K))
    (E : PolarParentJets (Linear K)) (C : Rat → K) :
    quadraticValue J Z (interpolateAngular C r k ell T P E) =
      evaluateAngular C r k ell T P E (linearValue J Z) := by
  simp only [interpolateAngular, recoverRow, evaluateAngular, angularRicciCoefficient, mapJet,
    mapPolarJets, quadraticValue, linearValue]
  ring

theorem conservation_rows_on_parent (r k ell J : K) (hr : r ≠ 0) (hh : r-2 ≠ 0)
    (dr : d r = 1) (wave : lapse r*d (lapse r*d J) = (k^2+parentPotential r ell)*J) :
    let Z := r^2*(lapse r*d J)
    let T := radialJet d (lapse r*d (r*J)/2)
    let P := radialJet d (-(k*r)*J/(2*lapse r))
    let E := scalarPolarReconstruction d r k ell (referenceEven r k ell J Z)
    let v := vectorValue r k ell T P E
    quadraticValue J Z (conservationRows (fun q => (q : K)) d r k ell) =
      d (r*r*lapse r*v.radius) + (2*k*r*r/lapse r)*v.time -
        ((ell+1)/ell)*angularRicciValue r k ell T P E := by
  let Z := r^2*(lapse r*d J)
  let t := parentJet d r k ell (timeAmplitude r)
  let p := parentJet d r k ell (radiusAmplitude r k)
  let e := polarReconstruction d r k ell
  let C : Rat → K := fun q => (q : K)
  let T := radialJet d (lapse r*d (r*J)/2)
  let P := radialJet d (-(k*r)*J/(2*lapse r))
  let E := scalarPolarReconstruction d r k ell (referenceEven r k ell J Z)
  obtain ⟨hJ,hZ,hT,hP⟩ := rw_parent_jet_rules d r k ell J hr hh dr wave
  have tEq : linearValue J Z (timeAmplitude r) = lapse r*d (r*J)/2 := hT
  have pEq : linearValue J Z (radiusAmplitude r k) = -(k*r)*J/(2*lapse r) := hP
  have time : mapJet (linearValue J Z) t = T := by
    simpa only [t, T, radialJet, tEq] using parent_jet_value d r k ell J Z hJ hZ (timeAmplitude r)
  have radius : mapJet (linearValue J Z) p = P := by
    simpa only [p, P, radialJet, pEq] using parent_jet_value d r k ell J Z hJ hZ (radiusAmplitude r k)
  have polar : mapPolarJets (linearValue J Z) e = E :=
    polar_reconstruction_value d r k ell J Z hJ hZ
  have vector : vectorSamples C r k ell t p e J Z = vectorValue r k ell T P E := by
    have folded : (fun q : Linear K => q.1*J+q.2*Z) = linearValue J Z := rfl
    simp only [vectorSamples, evaluateVector, folded, time, radius, polar, vectorValue, C,
      OfNat.ofNat, Nat.cast_one]
  have angular : evaluateAngular C r k ell t p e (linearValue J Z) = angularRicciValue r k ell T P E := by
    simp only [evaluateAngular, time, radius, polar, angularRicciValue, C,
      OfNat.ofNat, Nat.cast_one]
  obtain ⟨ht,hp⟩ := vector_interpolation r k ell J Z t p e C
  rw [vector] at ht hp
  have ha := (angular_interpolation r k ell J Z t p e C).trans angular
  simp only [t, p, e] at ht hp ha
  let v := vectorValue r k ell T P E
  change quadraticValue J Z (conservationRows C d r k ell) =
    d (r*r*lapse r*v.radius) + (2*k*r*r/lapse r)*v.time -
      ((ell+1)/ell)*angularRicciValue r k ell T P E
  simp only [conservationRows, reconstructedVector, reconstructedAngular, row_value_add,
    row_derivative_value d r k ell J Z hJ hZ, row_value_scale, ht, hp, ha, v]
  simp only [OfNat.ofNat, Nat.cast_one]
  ring

#print axioms conservation_rows_on_parent

end
end SchwarzschildEinstein.PureOdd.Mixed
