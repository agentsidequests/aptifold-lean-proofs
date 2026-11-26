import ParityReconstructionInverse
import ParityReconstructionResidual

/-! The sourced master equations suffice for local metric
reconstruction once the source satisfies its harmonic conservation laws. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

local notation "f" => radialLapse

private theorem polar_constraints (r w m e : K) (s : ModeSource K) (a : Mixed.AxialVector K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0)
    (dr : D r = 1) (dm : D m = 0) :
    let p := reconstructPolar D r w m e s
    let G := radialModeEinstein D r w m p a
    G.polar.tt = s.polar.tt ∧ G.tr = s.tr ∧ G.polar.traceFree = s.polar.traceFree := by
  let p := reconstructPolar D r w m e s
  let G := radialModeEinstein D r w m p a
  have hf : f r ≠ 0 := div_ne_zero hh hr
  have h2 : (2 : K) ≠ 0 := by norm_num
  have em : evenMasterField D r m p.rr p.sphere = e :=
    even_master_of_reconstruction D r w m e s hr hf hl hp
  have sphere := sphere_of_metric D r w m p hr hl hp dr dm
  change sphereFromMaster D r m (evenMasterField D r m p.rr p.sphere) G.polar.tt =
    p.sphere/r^2 at sphere
  have expected : p.sphere/r^2 = sphereFromMaster D r m e s.polar.tt :=
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hr)
  rw [em, expected] at sphere
  have tt : G.polar.tt = s.polar.tt := by
    have coeff : 2*r^3/(m*(m+1)*(modeLambda m*r+3)) ≠ 0 :=
      div_ne_zero (mul_ne_zero h2 (pow_ne_zero 3 hr)) (mul_ne_zero hl hp)
    simpa only [sphereFromMaster, sub_right_inj, mul_right_inj' coeff] using sphere
  have tr : G.tr = s.tr := by
    have cross := cross_of_metric D r w m p a hr hh hl hp dr dm
    change crossFromMaster D r w m (evenMasterField D r m p.rr p.sphere) G.polar.tt G.tr = p.tr at cross
    have expectedCross : p.tr = crossFromMaster D r w m e s.polar.tt s.tr := rfl
    rw [em, tt, expectedCross] at cross
    have coeff : 2*r^2/(m*(m+1)) ≠ 0 :=
      div_ne_zero (mul_ne_zero h2 (pow_ne_zero 2 hr)) hl
    unfold crossFromMaster at cross
    exact add_right_cancel ((mul_right_inj' coeff).mp (add_left_cancel cross))
  have tf : G.polar.traceFree = s.polar.traceFree := by
    have ptt : p.tt = (f r)^2*p.rr+2*f r*s.polar.traceFree := rfl
    change (↑(1/2 : ℚ) : K)*(r*(1/(r-2))*p.tt + -(((r + -↑(2 : ℚ))*(1/r))*p.rr)) =
      s.polar.traceFree
    rw [ptt]
    norm_num [PureOdd.lapse]
    field_simp [hr, hh]
    ring
  exact ⟨tt,tr,tf⟩

private theorem axial_constraints (r w m o : K) (p : PolarAmplitudes K) (s : Mixed.AxialVector K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hm : (m-1)*(m+2) ≠ 0)
    (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)
    (wave : waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) o =
      oddMasterForcing D r w m s) :
    let a := reconstructAxial D r w m o s
    oddMasterField D r w m a.time a.radius = o ∧ (radialModeEinstein D r w m p a).axial = s := by
  let a := reconstructAxial D r w m o s
  let G := radialModeEinstein D r w m p a
  have om : oddMasterField D r w m a.time a.radius = o := by
    have h := odd_master_of_reconstruction D r w m o s hr hh hm dr dm
    simpa only [wave, sub_self, mul_zero, add_zero] using h
  have matched := axial_of_metric D r w m a hr hh hm dr dw dm
  change reconstructAxial D r w m (oddMasterField D r w m a.time a.radius) G.axial =
    reconstructAxial D r w m o s at matched
  rw [om] at matched
  have h2 : (2 : K) ≠ 0 := by norm_num
  have coeff := div_ne_zero (mul_ne_zero h2 (pow_ne_zero 2 hr)) hm
  have eqTime : G.axial.time = s.time := by
    have h := congrArg Mixed.AxialVector.time matched
    exact (mul_right_inj' coeff).mp (add_left_cancel h)
  have eqRadius : G.axial.radius = s.radius := by
    have h := congrArg Mixed.AxialVector.radius matched
    exact (mul_right_inj' coeff).mp (add_left_cancel h)
  refine ⟨om, ?_⟩
  revert eqTime eqRadius
  generalize G.axial = v
  cases v
  cases s
  simp
  exact fun t v => ⟨t,v⟩

theorem sourced_mode_reconstruction (r w m e o : K) (s : ModeSource K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hl : m*(m+1) ≠ 0) (hmu : (m-1)*(m+2) ≠ 0)
    (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1) (dw : D w = 0) (dm : D m = 0)
    (conservation : ConservedMode D r w m s)
    (even : waveResidual D r w (SchwarzschildEinstein.zerilli r (modeLambda m)) e =
      evenMasterForcing D r m s.polar)
    (odd : waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) o =
      oddMasterForcing D r w m s.axial) :
    let p := reconstructPolar D r w m e s
    let a := reconstructAxial D r w m o s.axial
    radialModeEinstein D r w m p a = s ∧
      evenMasterField D r m p.rr p.sphere = e ∧ oddMasterField D r w m a.time a.radius = o := by
  let p := reconstructPolar D r w m e s
  let a := reconstructAxial D r w m o s.axial
  let G := radialModeEinstein D r w m p a
  have hf : f r ≠ 0 := div_ne_zero hh hr
  have em : evenMasterField D r m p.rr p.sphere = e :=
    even_master_of_reconstruction D r w m e s hr hf hl hp
  obtain ⟨om, ax⟩ := axial_constraints D r w m o p s.axial hr hh hmu dr dw dm odd
  obtain ⟨tt,tr,tf⟩ := polar_constraints D r w m e s a hr hh hl hp dr dm
  have actualEven := even_radial_projection D r w m p.tt p.tr p.rr p.sphere hr hh hl hp dr dw dm
  change waveResidual D r w (SchwarzschildEinstein.zerilli r (modeLambda m))
    (evenMasterField D r m p.rr p.sphere) = evenMasterForcing D r m G.polar at actualEven
  rw [em, even] at actualEven
  have difference := conserved_difference D r w m G s
    (radial_einstein_conserved D r w m p a hr hh dr dw dm) conservation
  have forcing : evenMasterForcing D r m (sourceDifference G s).polar = 0 := by
    change evenMasterForcing D r m (polarDifference G.polar s.polar) = 0
    rw [even_forcing_difference, ← actualEven, sub_self]
  have zero := conserved_residual_zero D r w m (sourceDifference G s) hr hf hl hmu hp dr difference
    (sub_eq_zero.mpr tt) (sub_eq_zero.mpr tr) (sub_eq_zero.mpr tf)
    (sub_eq_zero.mpr (congrArg Mixed.AxialVector.time ax))
    (sub_eq_zero.mpr (congrArg Mixed.AxialVector.radius ax)) forcing
  exact ⟨(source_difference_eq_zero G s).mp zero, em, om⟩

#print axioms sourced_mode_reconstruction

end
end SchwarzschildEinstein.PureOdd.Master
