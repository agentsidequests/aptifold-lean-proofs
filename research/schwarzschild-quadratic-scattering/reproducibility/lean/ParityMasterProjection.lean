import ParityMasterRadial
import ParityMasterReadout

/-! The two scalar equations follow from the sourced coordinate
Einstein equation in Regge–Wheeler gauge. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

def radialGaugeMetric (w m htt htr hrr sphere T P : K) : SecondMetric K :=
  reggeWheelerGaugeMetric w m (Mixed.radialJet D T) (Mixed.radialJet D P)
    ⟨Mixed.radialJet D htt,Mixed.radialJet D htr,Mixed.radialJet D hrr,Mixed.radialJet D sphere⟩

omit [CharZero K] [Algebra ℚ K] in
private theorem lapse_agrees (r : K) (hr : r ≠ 0) :
    PureOdd.lapse r = SchwarzschildEinstein.lapse r := by
  unfold PureOdd.lapse SchwarzschildEinstein.lapse
  field_simp [hr]

theorem parity_master_equations (r w m htt htr hrr sphere T P : K) (S : Tensor Axis K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hl : m*(m+1) ≠ 0) (hmu : (m-1)*(m+2) ≠ 0)
    (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)
    (source : equatorialEinstein r (radialGaugeMetric D w m htt htr hrr sphere T P) = S) :
    waveResidual D r w (SchwarzschildEinstein.zerilli r (modeLambda m)) (evenMasterField D r m hrr sphere) =
      evenMasterForcing D r m (polarSourceReadout m S) ∧
    waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) (oddMasterField D r w m T P) =
      oddMasterForcing D r w m (axialSourceReadout m S) := by
  have hm := (mul_ne_zero_iff.mp hl).1
  have hprev := (mul_ne_zero_iff.mp hmu).1
  unfold radialGaugeMetric at source
  rw [← source, polar_readout_from_tensor _ _ _ _ _ _ hr hh hm hprev,
    axial_readout_from_tensor _ _ _ _ _ _ hr hh hm]
  exact ⟨even_radial_projection D r w m htt htr hrr sphere hr hh hl hp dr dw dm,
    odd_radial_projection D r w m T P hr hh hmu dr dw dm⟩

theorem even_forcing_in_manuscript_convention (r ell : K) (s : EvenSource K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hp : modeLambda (2*ell)*r+3 ≠ 0) :
    evenMasterForcing D r (2*ell) s = evenMasterValue D r ell s := by
  have cap_eq : (2*ell-1)*(2*ell+2)+6/r = 2*(modeLambda (2*ell)*r+3)/r := by
    unfold modeLambda
    field_simp [hr]
    ring
  have hf : PureOdd.lapse r ≠ 0 := div_ne_zero hh hr
  have trace_eq : orbitHalfTrace r s =
      -(1/(2*PureOdd.lapse r))*s.tt+PureOdd.lapse r/2*s.rr := by
    unfold orbitHalfTrace
    field_simp [hf]
  simp only [evenMasterForcing, evenMasterValue, cap_eq, trace_eq]
  generalize pole_eq : modeLambda (2*ell)*r+3 = pole at hp ⊢
  field_simp [hr, hp]
  ring

omit [CharZero K] in
theorem odd_forcing_in_manuscript_convention (r k ell : K) (s : Mixed.AxialVector K) :
    oddMasterForcing D r (2*k) (2*ell) s = -Mixed.mixedMaster D r k ell s := by
  have unit : @OfNat.ofNat K 1 (Mixed.instOfNat_mixedRadialFormulas 1) = (1 : K) := Nat.cast_one
  unfold oddMasterForcing Mixed.mixedMaster Mixed.oddMasterScale
  simp only [neg_mul, radialLapse, unit]

theorem projected_forcing_in_manuscript_convention (r k ell phase : K) (S : Tensor Axis K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hp : modeLambda (2*ell)*r+3 ≠ 0) :
    let Dstar : Derivation ℚ K K := PureOdd.lapse r • D
    let W := SchwarzschildEinstein.superpotential r (modeLambda (2*ell))
    let scale := SchwarzschildEinstein.algebraicFrequency (modeLambda (2*ell))-2*k
    let p := polarSourceReadout (2*ell) S
    let a := axialSourceReadout (2*ell) S
    SchwarzschildEinstein.toOdd Dstar W (evenMasterForcing D r (2*ell) p)/scale -
      phase*oddMasterForcing D r (2*k) (2*ell) a =
      projectedMasterValue D r k ell p + phase*Mixed.mixedMaster D r k ell a := by
  dsimp only
  rw [even_forcing_in_manuscript_convention _ _ _ _ hr hh hp,
    odd_forcing_in_manuscript_convention, mul_neg, sub_neg_eq_add]
  simp only [SchwarzschildEinstein.toOdd, SchwarzschildEinstein.superpotential,
    SchwarzschildEinstein.algebraicFrequency, Derivation.smul_apply, smul_eq_mul,
    projectedMasterValue, modeLambda, ← lapse_agrees r hr]

theorem common_odd_equation_of_tensor (r w m phase htt htr hrr sphere T P : K) (S : Tensor Axis K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hl : m*(m+1) ≠ 0) (hmu : (m-1)*(m+2) ≠ 0)
    (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)
    (dp : D phase = 0)
    (source : equatorialEinstein r (radialGaugeMetric D w m htt htr hrr sphere T P) = S) :
    let Dstar : Derivation ℚ K K := PureOdd.lapse r • D
    let W := SchwarzschildEinstein.superpotential r (modeLambda m)
    let scale := SchwarzschildEinstein.algebraicFrequency (modeLambda m)-w
    let e := evenMasterField D r m hrr sphere
    let o := oddMasterField D r w m T P
    let se := evenMasterForcing D r m (polarSourceReadout m S)
    let so := oddMasterForcing D r w m (axialSourceReadout m S)
    waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m))
      (SchwarzschildEinstein.toOdd Dstar W e/scale-phase*o) =
      SchwarzschildEinstein.toOdd Dstar W se/scale-phase*so := by
  let Dstar : Derivation ℚ K K := PureOdd.lapse r • D
  have radius : Dstar r = SchwarzschildEinstein.lapse r := by
    change PureOdd.lapse r*D r = _
    rw [dr, mul_one, lapse_agrees r hr]
  have mode : Dstar (modeLambda m) = 0 := by
    change PureOdd.lapse r*D (modeLambda m) = 0
    have c : D (2 : K) = 0 := D.map_natCast 2
    simp [modeLambda, D.leibniz_div_const _ _ c, D.leibniz, smul_eq_mul, dm, c]
  have frequency : Dstar w = 0 := by change PureOdd.lapse r*D w = 0; rw [dw, mul_zero]
  have phase_const : Dstar phase = 0 := by change PureOdd.lapse r*D phase = 0; rw [dp, mul_zero]
  obtain ⟨even,odd⟩ := parity_master_equations D r w m htt htr hrr sphere T P S hr hh hl hmu hp dr dw dm source
  exact SchwarzschildEinstein.schwarzschild_projected_source Dstar r (modeLambda m) w phase
    _ _ _ _ hr hp radius mode frequency phase_const even odd

#print axioms parity_master_equations
#print axioms even_forcing_in_manuscript_convention
#print axioms odd_forcing_in_manuscript_convention
#print axioms projected_forcing_in_manuscript_convention
#print axioms common_odd_equation_of_tensor

end
end SchwarzschildEinstein.PureOdd.Master
