import QuadraticConservationRows
import ParityReconstructionConservation
import MixedRadialCalculus
import MixedSourceReadouts

/-! Radial data and conservation balances for the bare scattering source.
The coordinate identities can be checked separately from its divergence. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type} [Field K] [CharZero K] [Algebra ℚ K]

local notation "C" => (fun q : Rat => (q : K))

def scatteringPolarParent (D : Derivation ℚ K K) (r k ell J : K) : Mixed.PolarParentJets K :=
  Mixed.scalarPolarReconstruction D r k ell (Mixed.referenceEven r k ell J (r^2*(lapse r*D J)))

def scatteringAxialTime (D : Derivation ℚ K K) (r J : K) : RadialJet K :=
  Mixed.radialJet D (lapse r*D (r*J)/2)

def scatteringAxialRadius (D : Derivation ℚ K K) (r k J : K) : RadialJet K :=
  Mixed.radialJet D (-(k*r)*J/(2*lapse r))

def evenScatteringSource (D : Derivation ℚ K K) (r k ell J : K) : ModeSource K :=
  mapModeSource (quadraticValue J (r^2*(lapse r*D J))) (evenParentSourceRows C D r k ell)

def oddScatteringSource (D : Derivation ℚ K K) (r k ell J : K) : ModeSource K :=
  mapModeSource (quadraticValue J (r^2*(lapse r*D J))) (oddParentSourceRows C D r k ell)

def mixedScatteringSource (D : Derivation ℚ K K) (r k ell J : K) : ModeSource K :=
  let T := scatteringAxialTime D r J
  let P := scatteringAxialRadius D r k J
  let E := scatteringPolarParent D r k ell J
  pureAxialSource 0 (Mixed.vectorValue r k ell T P E) (Mixed.axialAngularCoefficient r k ell T P E)

def quadraticModeCombination (a b : K) (E M O : ModeSource K) : ModeSource K :=
  let value := fun x y z => a^2*x+a*b*y+b^2*z
  ⟨⟨value E.polar.tt M.polar.tt O.polar.tt, value E.polar.rr M.polar.rr O.polar.rr,
     value E.polar.radialVector M.polar.radialVector O.polar.radialVector,
     value E.polar.sphereTrace M.polar.sphereTrace O.polar.sphereTrace,
     value E.polar.traceFree M.polar.traceFree O.polar.traceFree⟩,
   value E.tr M.tr O.tr, value E.timeVector M.timeVector O.timeVector,
   ⟨value E.axial.time M.axial.time O.axial.time, value E.axial.radius M.axial.radius O.axial.radius⟩,
   value E.axialTensor M.axialTensor O.axialTensor⟩

def bareScatteringSource (D : Derivation ℚ K K) (r k ell J a beta : K) : ModeSource K :=
  quadraticModeCombination a beta (evenScatteringSource D r k ell J)
    (mixedScatteringSource D r k ell J) (oddScatteringSource D r k ell J)

section Polar

variable (D : Derivation ℚ K K) (r k ell J Z : K)
variable (hJ : D J = jetU r*Z) (hZ : D Z = jetV r k ell*J+jetW r*Z)

include hJ hZ in
private theorem conservation_rows_value (s : ModeSource (Quadratic K)) :
    let p := polarConservationRows C D r k ell s
    let u := mapModeSource (quadraticValue J Z) s
    quadraticValue J Z p.1 = timeBalance D r (2*k) (2*ell) u ∧
    quadraticValue J Z p.2.1 = radiusBalance D r (2*k) (2*ell) u ∧
    quadraticValue J Z p.2.2 = polarBalance D r (2*k) (2*ell) u := by
  dsimp only [polarConservationRows]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Mixed.row_value_add, Mixed.row_value_scale, row_derivative_value D r k ell J Z hJ hZ,
      mapModeSource, timeBalance, radiusBalance, polarBalance, vectorDivergence, radialLapse,
      Rat.cast_ofNat, Rat.cast_one, pow_succ, pow_zero, one_mul] <;> ring

include hJ hZ in
theorem polar_zero_balances (s : ModeSource (Quadratic K))
    (zero : polarConservationRows C D r k ell s = ((0,0,0),(0,0,0),(0,0,0))) :
    let u := mapModeSource (quadraticValue J Z) s
    timeBalance D r (2*k) (2*ell) u = 0 ∧ radiusBalance D r (2*k) (2*ell) u = 0 ∧
    polarBalance D r (2*k) (2*ell) u = 0 := by
  have balance := conservation_rows_value D r k ell J Z hJ hZ s
  dsimp only at balance
  rw [zero] at balance
  simp only [quadraticValue, zero_mul, zero_add] at balance
  exact ⟨balance.1.symm,balance.2.1.symm,balance.2.2.symm⟩

end Polar

theorem mixed_axial_balance (D : Derivation ℚ K K) (r k ell : K)
    (v : Mixed.AxialVector K) (s : K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (dr : D r = 1)
    (conserved : D (r*r*lapse r*v.radius) + (2*k*r*r/lapse r)*v.time =
      ((2*ell-1)*(2*ell+2)/2)*s) :
    axialBalance D r (2*k) (2*ell) (pureAxialSource 0 v s) = 0 := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hr))
  rw [mul_zero]
  have factor : r*r*lapse r = r*(r-2) := by
    simp only [lapse]
    field_simp [hr]
  have product : D (r*r*lapse r*v.radius) + (2*k*r*r/lapse r)*v.time -
      ((2*ell-1)*(2*ell+2)/2)*s =
        r^2*axialBalance D r (2*k) (2*ell) (pureAxialSource 0 v s) := by
    rw [factor, D.leibniz, D.leibniz, map_sub, derivative_two D, dr]
    simp only [axialBalance, vectorDivergence, radialLapse, pureAxialSource, smul_eq_mul, lapse]
    field_simp [hr, hh]
    ring
  rw [← product, conserved, sub_self]

end
end SchwarzschildEinstein.PureOdd.Master
