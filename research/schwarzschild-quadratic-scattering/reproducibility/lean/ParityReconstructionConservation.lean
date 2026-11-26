import ParityReconstruction

/-! The four harmonic components of the source conservation equation
in areal radius. These versions use covariant orbit components. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

local notation "f" => radialLapse

def timeBalance (r w m : K) (s : ModeSource K) : K :=
  w/f r*s.polar.tt + f r*D s.tr + (2/r^2+2*f r/r)*s.tr - m*(m+1)/r^2*s.timeVector

def radiusBalance (r w m : K) (s : ModeSource K) : K :=
  f r*D s.polar.rr + (3/r^2+2*f r/r)*s.polar.rr + s.polar.tt/(r^2*(f r)^2) +
    w/f r*s.tr - m*(m+1)/r^2*s.polar.radialVector - 2/r^3*s.polar.sphereTrace

def vectorDivergence (r w t v : K) : K :=
  w/f r*t + f r*D v + (2/r^2+2*f r/r)*v

def polarBalance (r w m : K) (s : ModeSource K) : K :=
  vectorDivergence D r w s.timeVector s.polar.radialVector +
    s.polar.sphereTrace/r^2 - (m-1)*(m+2)/(2*r^2)*s.polar.traceFree

def axialBalance (r w m : K) (s : ModeSource K) : K :=
  vectorDivergence D r w s.axial.time s.axial.radius -
    (m-1)*(m+2)/(2*r^2)*s.axialTensor

structure ConservedMode (r w m : K) (s : ModeSource K) : Prop where
  time : timeBalance D r w m s = 0
  radius : radiusBalance D r w m s = 0
  polar : polarBalance D r w m s = 0
  axial : axialBalance D r w m s = 0

def polarDifference (a b : EvenSource K) : EvenSource K :=
  ⟨a.tt-b.tt,a.rr-b.rr,a.radialVector-b.radialVector,a.sphereTrace-b.sphereTrace,a.traceFree-b.traceFree⟩

def sourceDifference (a b : ModeSource K) : ModeSource K :=
  ⟨polarDifference a.polar b.polar,a.tr-b.tr,a.timeVector-b.timeVector,
    ⟨a.axial.time-b.axial.time,a.axial.radius-b.axial.radius⟩,a.axialTensor-b.axialTensor⟩

theorem conserved_difference (r w m : K) (a b : ModeSource K)
    (ha : ConservedMode D r w m a) (hb : ConservedMode D r w m b) :
    ConservedMode D r w m (sourceDifference a b) := by
  obtain ⟨atime, aradial, apolar, aaxial⟩ := ha
  obtain ⟨btime, bradial, bpolar, baxial⟩ := hb
  constructor
  · calc
      _ = timeBalance D r w m a - timeBalance D r w m b := by
        simp only [timeBalance, sourceDifference, polarDifference, map_sub]
        ring
      _ = 0 := by rw [atime, btime, sub_self]
  · calc
      _ = radiusBalance D r w m a - radiusBalance D r w m b := by
        simp only [radiusBalance, sourceDifference, polarDifference, map_sub, sub_div]
        ring
      _ = 0 := by rw [aradial, bradial, sub_self]
  · calc
      _ = polarBalance D r w m a - polarBalance D r w m b := by
        simp only [polarBalance, vectorDivergence, sourceDifference, polarDifference, map_sub, sub_div]
        ring
      _ = 0 := by rw [apolar, bpolar, sub_self]
  · calc
      _ = axialBalance D r w m a - axialBalance D r w m b := by
        simp only [axialBalance, vectorDivergence, sourceDifference, map_sub]
        ring
      _ = 0 := by rw [aaxial, baxial, sub_self]

section Bianchi

variable (r w m : K) (p : PolarAmplitudes K) (a : Mixed.AxialVector K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)

local notation "G" => radialModeEinstein D r w m p a

-- Each balance is checked independently on the free metric amplitudes.
set_option hygiene false in
local macro "verify_bianchi" : tactic => `(tactic| (
  simp only [timeBalance, radiusBalance, polarBalance, axialBalance, vectorDivergence,
    radialModeEinstein, modeEinstein, polarEinstein, axialEinstein, Mixed.radialJet, radialLapse,
    PureOdd.lapse, map_add, map_sub, map_neg, map_zero, D.map_one_eq_zero, D.leibniz,
    D.leibniz_div, D.leibniz_inv, derivative_rat, derivative_two, derivative_three,
    smul_eq_mul, pow_two, dr, dw, dm]
  simp only [zero_add, add_zero, mul_zero, zero_mul, one_mul, mul_one, neg_zero, zero_sub,
    sub_zero, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one]
  field_simp [hr, hh]
  ring))

include hr hh dr dw dm

set_option maxHeartbeats 600000 in
private theorem einstein_time_balance : timeBalance D r w m G = 0 := by verify_bianchi

set_option maxHeartbeats 600000 in
private theorem einstein_radius_balance : radiusBalance D r w m G = 0 := by verify_bianchi

set_option maxHeartbeats 600000 in
set_option linter.unusedSectionVars false in
private theorem einstein_polar_balance : polarBalance D r w m G = 0 := by verify_bianchi

set_option maxHeartbeats 600000 in
private theorem einstein_axial_balance : axialBalance D r w m G = 0 := by verify_bianchi

theorem radial_einstein_conserved : ConservedMode D r w m G :=
  ⟨einstein_time_balance D r w m p a hr hh dr dw dm,
   einstein_radius_balance D r w m p a hr hh dr dw dm,
   einstein_polar_balance D r w m p a hr hh dr dw dm,
   einstein_axial_balance D r w m p a hr hh dr dw dm⟩

end Bianchi

#print axioms conserved_difference
#print axioms radial_einstein_conserved

end
end SchwarzschildEinstein.PureOdd.Master
