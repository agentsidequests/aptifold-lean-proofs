import PureOddFormulas
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Interpret coefficient triples on a Regge–Wheeler parent and its
radial derivative. These identities are independent of the detailed
tensor contractions. -/
namespace SchwarzschildEinstein.PureOdd

noncomputable section

variable {K : Type*} [Field K]

private theorem formula_zero :
    @OfNat.ofNat K 0 (instOfNat_pureOddFormulas 0) = (0 : K) :=
  Nat.cast_zero

private theorem formula_one :
    @OfNat.ofNat K 1 (instOfNat_pureOddFormulas 1) = (1 : K) :=
  Nat.cast_one

def linearValue (J Z : K) (p : Linear K) : K := p.1*J+p.2*Z
def quadraticValue (J Z : K) (p : Quadratic K) : K := p.1*J^2+p.2.1*J*Z+p.2.2*Z^2

private theorem quadratic_add (J Z : K) (p q : Quadratic K) :
    quadraticValue J Z (plus p q) = quadraticValue J Z p+quadraticValue J Z q := by
  simp only [quadraticValue, plus]
  ring

private theorem quadratic_sub (J Z : K) (p q : Quadratic K) :
    quadraticValue J Z (minus p q) = quadraticValue J Z p-quadraticValue J Z q := by
  simp only [quadraticValue, minus]
  ring

private theorem quadratic_scale (J Z a : K) (p : Quadratic K) :
    quadraticValue J Z (scale a p) = a*quadraticValue J Z p := by
  simp only [quadraticValue, scale, mapRow]
  ring

variable [Algebra ℚ K] (d : Derivation ℚ K K)

theorem linear_derivative_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z)
    (p : Linear K) :
    linearValue J Z (linearDerivative d r k ell p) = d (linearValue J Z p) := by
  rcases p with ⟨a,b⟩
  simp only [linearValue, linearDerivative, map_add, d.leibniz, smul_eq_mul, hJ, hZ]
  ring

theorem row_derivative_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z)
    (p : Quadratic K) :
    quadraticValue J Z (rowDerivative d r k ell p) = d (quadraticValue J Z p) := by
  rcases p with ⟨a,b,c⟩
  simp only [quadraticValue, rowDerivative, pow_two, map_add, d.leibniz, smul_eq_mul, hJ, hZ]
  ring

theorem parent_jet_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z) (p : Linear K) :
    let val := linearValue J Z p
    mapJet (linearValue J Z) (parentJet d r k ell p) = ⟨val, d val, d (d val)⟩ := by
  simp only [parentJet, mapJet, linear_derivative_value d r k ell J Z hJ hZ]

def sourceValue (J Z : K) (s : EvenSource (Quadratic K)) : EvenSource K :=
  let ev := quadraticValue J Z
  ⟨ev s.tt, ev s.rr, ev s.radialVector, ev s.sphereTrace, ev s.traceFree⟩

def evenMasterValue (r ell : K) (s : EvenSource K) : K :=
  let L := 2*ell
  let L2 := L*(L+1)
  let mu := (L-1)*(L+2)
  let cap := mu+6/r
  let f := lapse r
  let bullet := -(1/(2*f))*s.tt+f/2*s.rr
  let inside := 24*f^2/cap*s.rr-4*r^2*f*d bullet+4*f/r*s.sphereTrace+
    2*r/cap*(mu*(mu-2)+12*(mu-3)/r+84/r^2)*bullet
  f*(8*f/cap*s.radialVector-2/r*s.traceFree+2/(L2*cap)*inside)

def projectedMasterValue (r k ell : K) (s : EvenSource K) : K :=
  let L := 2*ell
  let lam := (L-1)*(L+2)/2
  let gamma := lam*(lam+1)/3
  let W := gamma+3*lapse r/(r*(lam*r+3))
  let even := evenMasterValue d r ell s
  (W*even-lapse r*d even)/(gamma-2*k)

variable [CharZero K]

private theorem even_master_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z)
    (s : EvenSource (Quadratic K)) :
    quadraticValue J Z (evenMaster d r k ell s) = evenMasterValue d r ell (sourceValue J Z s) := by
  simp only [evenMaster, evenMasterValue, sourceValue, quadratic_add, quadratic_scale,
    row_derivative_value d r k ell J Z hJ hZ, formula_one]
  ring

theorem projected_master_value (r k ell J Z : K)
    (hJ : d J = jetU r*Z) (hZ : d Z = jetV r k ell*J+jetW r*Z)
    (s : EvenSource (Quadratic K)) :
    quadraticValue J Z (projectedMaster d r k ell s) =
      projectedMasterValue d r k ell (sourceValue J Z s) := by
  simp only [projectedMaster, projectedMasterValue, quadratic_scale, quadratic_sub,
    row_derivative_value d r k ell J Z hJ hZ, even_master_value d r k ell J Z hJ hZ,
    formula_one, div_eq_mul_inv]
  ring

/-- Recover the two derivative rules and the axial amplitudes from the
odd parent equation. -/
theorem rw_parent_jet_rules (r k ell J : K) (hr : r ≠ 0) (hh : r-2 ≠ 0)
    (dr : d r = 1)
    (wave : lapse r*d (lapse r*d J) = (k^2+parentPotential r ell)*J) :
    let Z := r^2*(lapse r*d J)
    d J = jetU r*Z ∧
      d Z = jetV r k ell*J+jetW r*Z ∧
      linearValue J Z (timeAmplitude r) = lapse r*d (r*J)/2 ∧
      linearValue J Z (radiusAmplitude r k) = -(k*r)*J/(2*lapse r) := by
  let Z := r^2*(lapse r*d J)
  have hf : lapse r ≠ 0 := div_ne_zero hh hr
  have hderivative : d (lapse r*d J) = (k^2+parentPotential r ell)*J/lapse r := by
    apply (eq_div_iff hf).mpr
    rw [mul_comm, wave]
  have hsquare : d (r^2) = 2*r := by
    simp only [pow_two, d.leibniz, smul_eq_mul, dr, mul_one]
    ring
  change d J = jetU r*Z ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [jetU, Z, formula_one]
    field_simp [hr, hf]
  · dsimp only [Z, jetV, jetW]
    rw [d.leibniz, smul_eq_mul, smul_eq_mul, hsquare, hderivative]
    field_simp [hr, hf]
  · simp only [linearValue, timeAmplitude, d.leibniz, smul_eq_mul, dr, formula_one]
    field_simp [hr]
    ring
  · simp only [linearValue, radiusAmplitude, formula_zero, zero_mul, add_zero]
    ring

#print axioms linear_derivative_value
#print axioms row_derivative_value
#print axioms projected_master_value
#print axioms rw_parent_jet_rules

end
end SchwarzschildEinstein.PureOdd
