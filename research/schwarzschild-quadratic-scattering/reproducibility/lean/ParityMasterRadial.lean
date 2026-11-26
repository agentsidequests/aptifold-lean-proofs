import ParityMasterData
import PureOddRowCalculus
import MixedRadialFormulas
import EinsteinProjection

/-! Project the sourced linear Einstein equations to the two wave
operators. The radial amplitudes in the metric are free field elements. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

set_option maxRecDepth 12000

def modeLambda (m : K) : K := (m-1)*(m+2)/2
abbrev radialLapse (r : K) : K := PureOdd.lapse r
local notation "f" => radialLapse
private def radialPartial (r x : K) : K := f r*D x
def waveResidual (r w potential x : K) : K :=
  radialPartial D r (radialPartial D r x) - (w^2+potential)*x

def evenMasterField (r m hrr sphere : K) : K :=
  let scalar := sphere/r^2
  2*r/(m*(m+1))*(scalar+r/(modeLambda m*r+3)*(f r^2*hrr-r*f r*D scalar))

def oddMasterField (r w m T P : K) : K :=
  2*r/((m-1)*(m+2))*(D T+w*P-2*T/r)

def orbitHalfTrace (r : K) (s : EvenSource K) : K :=
  (-s.tt/(f r)+f r*s.rr)/2

def evenMasterForcing (r m : K) (s : EvenSource K) : K :=
  let pole := modeLambda m*r+3
  let mu := (m-1)*(m+2)
  let halfTrace := orbitHalfTrace r s
  let inside := 12*(f r)^2*r/pole*s.rr-4*r^2*f r*D halfTrace+4*f r/r*s.sphereTrace +
    r^2/pole*(mu*(mu-2)+12*(mu-3)/r+84/r^2)*halfTrace
  f r*(4*r*f r/pole*s.radialVector-2/r*s.traceFree+r/(m*(m+1)*pole)*inside)

def oddMasterForcing (r w m : K) (s : Mixed.AxialVector K) : K :=
  -(4*r*f r/((m-1)*(m+2)))*(D s.time+w*s.radius)

def polarJetReadout (r w m htt htr hrr sphere : K) : EvenSource K :=
  polarEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2))
    ⟨Mixed.radialJet D htt, Mixed.radialJet D htr, Mixed.radialJet D hrr, Mixed.radialJet D sphere⟩

def axialJetReadout (r w m T P : K) : Mixed.AxialVector K :=
  let G := axialEinstein (fun q => (q : K)) r w m (1/r) (1/(r-2)) (Mixed.radialJet D T) (Mixed.radialJet D P)
  ⟨-G.time,-G.radius⟩

omit [CharZero K] in
theorem derivative_rat (q : ℚ) : D (q : K) = 0 := by
  simpa only [eq_ratCast] using D.map_algebraMap q

omit [CharZero K] in
theorem derivative_two : D (2 : K) = 0 := D.map_natCast 2
omit [CharZero K] in
theorem derivative_three : D (3 : K) = 0 := D.map_natCast 3

theorem odd_radial_projection (r w m T P : K) (hr : r ≠ 0) (hh : r-2 ≠ 0)
    (mu : (m-1)*(m+2) ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0) :
    waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) (oddMasterField D r w m T P) =
      oddMasterForcing D r w m (axialJetReadout D r w m T P) := by
  simp [waveResidual, radialPartial, SchwarzschildEinstein.reggeWheeler, modeLambda, oddMasterField,
    oddMasterForcing, axialJetReadout, axialEinstein, Mixed.radialJet, radialLapse, PureOdd.lapse, SchwarzschildEinstein.lapse,
    D.leibniz, D.leibniz_div, D.leibniz_inv, derivative_two, pow_succ,
    smul_eq_mul, dr, dw, dm]
  obtain ⟨hm, hm'⟩ := mul_ne_zero_iff.mp mu
  field_simp [hr, hh, hm, hm']
  ring

private def addSource (a b : EvenSource K) : EvenSource K :=
  ⟨a.tt+b.tt,a.rr+b.rr,a.radialVector+b.radialVector,a.sphereTrace+b.sphereTrace,a.traceFree+b.traceFree⟩

private theorem polar_readout_add (r w m a b c s A B C S : K) :
    polarJetReadout D r w m (a+A) (b+B) (c+C) (s+S) =
      addSource (polarJetReadout D r w m a b c s) (polarJetReadout D r w m A B C S) := by
  simp [polarJetReadout, polarEinstein, Mixed.radialJet, addSource]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

private theorem even_forcing_add (r m : K) (a b : EvenSource K) :
    evenMasterForcing D r m (addSource a b) =
      evenMasterForcing D r m a + evenMasterForcing D r m b := by
  have trace : orbitHalfTrace r (addSource a b) = orbitHalfTrace r a + orbitHalfTrace r b := by
    simp only [orbitHalfTrace, addSource]
    ring
  unfold evenMasterForcing
  simp only [trace, map_add]
  simp only [addSource]
  ring

private theorem even_field_add (r m c s C S : K) :
    evenMasterField D r m (c+C) (s+S) = evenMasterField D r m c s + evenMasterField D r m C S := by
  simp only [evenMasterField, add_div, map_add]
  ring

omit [CharZero K] in
private theorem wave_residual_add (r w V a b : K) :
    waveResidual D r w V (a+b) = waveResidual D r w V a + waveResidual D r w V b := by
  simp only [waveResidual, radialPartial, map_add, mul_add, add_sub_add_comm]

private def evenResidual (r w m a b c s : K) : K :=
  waveResidual D r w (SchwarzschildEinstein.zerilli r (modeLambda m)) (evenMasterField D r m c s) -
    evenMasterForcing D r m (polarJetReadout D r w m a b c s)

private theorem even_residual_add (r w m a b c s A B C S : K) :
    evenResidual D r w m (a+A) (b+B) (c+C) (s+S) =
      evenResidual D r w m a b c s + evenResidual D r w m A B C S := by
  simp only [evenResidual, even_field_add, wave_residual_add, polar_readout_add, even_forcing_add, add_sub_add_comm]

section Columns

variable (r w m u : K) (hr : r ≠ 0) (hh : r-2 ≠ 0)
    (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)

-- Check each metric amplitude in its own declaration to bound elaboration memory.
set_option hygiene false in
local macro "verify_even_column" : tactic => `(tactic| (
  have dLambda : D (modeLambda m) = 0 := by
    simp [modeLambda, D.leibniz_div, D.leibniz, derivative_two, smul_eq_mul, dm]
  obtain ⟨hm, hm'⟩ := mul_ne_zero_iff.mp hl
  simp only [evenResidual, waveResidual, radialPartial, SchwarzschildEinstein.zerilli, evenMasterField,
    evenMasterForcing, orbitHalfTrace, polarJetReadout, polarEinstein, Mixed.radialJet, radialLapse,
    PureOdd.lapse, SchwarzschildEinstein.lapse, map_add, map_sub, map_neg, map_zero, D.map_one_eq_zero,
    D.leibniz, D.leibniz_div, D.leibniz_inv, derivative_rat, derivative_two, derivative_three,
    pow_two, smul_eq_mul, dr, dw, dm, dLambda]
  simp only [zero_add, add_zero, mul_zero, zero_mul, neg_zero, zero_sub, sub_zero, one_mul, mul_one,
    Rat.cast_ofNat, Rat.cast_div, Rat.cast_one]
  generalize pole_eq : modeLambda m*r+3 = pole at hp ⊢
  field_simp [hr, hh, hm, hm', hp]
  subst pole
  unfold modeLambda
  ring))

include hr hh hl hp dr dw dm

set_option maxHeartbeats 500000 in
private theorem even_time_column : evenResidual D r w m u 0 0 0 = 0 := by verify_even_column

set_option maxHeartbeats 500000 in
private theorem even_cross_column : evenResidual D r w m 0 u 0 0 = 0 := by verify_even_column

set_option maxHeartbeats 500000 in
private theorem even_radius_column : evenResidual D r w m 0 0 u 0 = 0 := by verify_even_column

set_option maxHeartbeats 500000 in
private theorem even_sphere_column : evenResidual D r w m 0 0 0 u = 0 := by verify_even_column

end Columns

theorem even_radial_projection (r w m htt htr hrr sphere : K) (hr : r ≠ 0) (hh : r-2 ≠ 0)
    (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0) :
    waveResidual D r w (SchwarzschildEinstein.zerilli r (modeLambda m)) (evenMasterField D r m hrr sphere) =
      evenMasterForcing D r m (polarJetReadout D r w m htt htr hrr sphere) := by
  have a := even_time_column D r w m htt hr hh hl hp dr dw dm
  have b := even_cross_column D r w m htr hr hh hl hp dr dw dm
  have c := even_radius_column D r w m hrr hr hh hl hp dr dw dm
  have s := even_sphere_column D r w m sphere hr hh hl hp dr dw dm
  have cs : evenResidual D r w m 0 0 hrr sphere = 0 := by
    simpa only [zero_add, add_zero, c, s] using even_residual_add D r w m 0 0 hrr 0 0 0 0 sphere
  have bcs : evenResidual D r w m 0 htr hrr sphere = 0 := by
    simpa only [zero_add, add_zero, b, cs] using even_residual_add D r w m 0 htr 0 0 0 0 hrr sphere
  have allInputs : evenResidual D r w m htt htr hrr sphere = 0 := by
    simpa only [zero_add, add_zero, a, bcs] using even_residual_add D r w m htt 0 0 0 0 htr hrr sphere
  exact sub_eq_zero.mp (by simpa only [evenResidual] using allInputs)

#print axioms odd_radial_projection
#print axioms even_radial_projection

end
end SchwarzschildEinstein.PureOdd.Master
