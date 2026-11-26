import ParityReconstruction

/-! Inversion of the master and constraint readouts. Recovering the
metric from its own readouts uses no master equation or boundary data. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

local notation "f" => radialLapse

set_option maxHeartbeats 600000 in
theorem sphere_of_metric (r w m : K) (p : PolarAmplitudes K)
    (hr : r ≠ 0) (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0)
    (dr : D r = 1) (dm : D m = 0) :
    sphereFromMaster D r m (evenMasterField D r m p.rr p.sphere)
      (polarJetReadout D r w m p.tt p.tr p.rr p.sphere).tt = p.sphere/r^2 := by
  have dLambda : D (modeLambda m) = 0 := by
    simp [modeLambda, D.leibniz_div, D.leibniz, derivative_two, smul_eq_mul, dm]
  simp only [sphereFromMaster, evenMasterField, polarJetReadout, polarEinstein, Mixed.radialJet,
    radialLapse, PureOdd.lapse, map_add, map_sub, D.map_one_eq_zero, D.leibniz, D.leibniz_div,
    D.leibniz_inv, derivative_two, derivative_three, smul_eq_mul, pow_two, dr, dm, dLambda]
  simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero,
    Rat.cast_ofNat, Rat.cast_div]
  generalize pole_eq : modeLambda m*r+3 = pole at hp ⊢
  obtain ⟨hm, hm'⟩ := mul_ne_zero_iff.mp hl
  field_simp [hr, hm, hm', hp]
  subst pole
  unfold modeLambda
  ring

omit [CharZero K] in
private theorem cross_in_terms_of_sphere (r w m e tt tr : K)
    (hr : r ≠ 0) (hf : f r ≠ 0) (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0) :
    crossFromMaster D r w m e tt tr =
      w*(modeLambda m*r+3)/(r*f r)*e - w*r/(f r)*sphereFromMaster D r m e tt +
      2*r^2/(m*(m+1))*tr := by
  simp only [crossFromMaster, sphereFromMaster]
  generalize pole_eq : modeLambda m*r+3 = pole at hp ⊢
  generalize f_eq : f r = F at hf ⊢
  obtain ⟨hm, hm'⟩ := mul_ne_zero_iff.mp hl
  field_simp [hr, hf, hm, hm', hp]
  subst pole
  ring

theorem cross_of_metric (r w m : K) (p : PolarAmplitudes K) (a : Mixed.AxialVector K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0)
    (dr : D r = 1) (dm : D m = 0) :
    let G := radialModeEinstein D r w m p a
    crossFromMaster D r w m (evenMasterField D r m p.rr p.sphere) G.polar.tt G.tr = p.tr := by
  have hf : f r ≠ 0 := div_ne_zero hh hr
  dsimp only
  rw [cross_in_terms_of_sphere D _ _ _ _ _ _ hr hf hl hp]
  have sphere := sphere_of_metric D r w m p hr hl hp dr dm
  change sphereFromMaster D r m (evenMasterField D r m p.rr p.sphere)
    (radialModeEinstein D r w m p a).polar.tt = p.sphere/r^2 at sphere
  rw [sphere]
  simp only [radialModeEinstein, modeEinstein, Mixed.radialJet, evenMasterField,
    radialLapse, PureOdd.lapse, smul_eq_mul, dr, D.leibniz, D.leibniz_div,
    pow_two, Rat.cast_ofNat, Rat.cast_div]
  obtain ⟨hm, hm'⟩ := mul_ne_zero_iff.mp hl
  generalize pole_eq : modeLambda m*r+3 = pole at hp ⊢
  field_simp [hr, hh, hm, hm', hp]
  subst pole
  unfold modeLambda
  ring

theorem even_master_of_reconstruction (r w m e : K) (s : ModeSource K)
    (hr : r ≠ 0) (hf : f r ≠ 0) (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0) :
    let p := reconstructPolar D r w m e s
    evenMasterField D r m p.rr p.sphere = e := by
  simp only [reconstructPolar, evenMasterField]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hr)]
  generalize scalar_eq : sphereFromMaster D r m e s.polar.tt = scalar
  generalize pole_eq : modeLambda m*r+3 = pole at hp ⊢
  generalize f_eq : f r = F at hf ⊢
  obtain ⟨hm, hm'⟩ := mul_ne_zero_iff.mp hl
  field_simp [hr, hf, hm, hm', hp]
  ring

theorem axial_of_metric (r w m : K) (a : Mixed.AxialVector K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hm : (m-1)*(m+2) ≠ 0)
    (dr : D r = 1) (dw : D w = 0) (dm : D m = 0) :
    reconstructAxial D r w m (oddMasterField D r w m a.time a.radius)
      (axialJetReadout D r w m a.time a.radius) = a := by
  cases a with
  | mk T P =>
    obtain ⟨hm',hm''⟩ := mul_ne_zero_iff.mp hm
    simp [reconstructAxial, oddMasterField, axialJetReadout, axialEinstein, Mixed.radialJet,
      radialLapse, PureOdd.lapse, D.leibniz, D.leibniz_div,
      derivative_two, smul_eq_mul, pow_succ, dr, dw, dm]
    constructor <;> field_simp [hr, hh, hm', hm''] <;> ring

theorem odd_master_of_reconstruction (r w m o : K) (s : Mixed.AxialVector K)
    (hr : r ≠ 0) (hh : r-2 ≠ 0) (hm : (m-1)*(m+2) ≠ 0)
    (dr : D r = 1) (dm : D m = 0) :
    let p := reconstructAxial D r w m o s
    oddMasterField D r w m p.time p.radius =
      o + r^2/(f r*((m-1)*(m+2))) *
        (waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) o -
          oddMasterForcing D r w m s) := by
  have wave : waveResidual D r w (SchwarzschildEinstein.reggeWheeler r (modeLambda m)) o =
      f r*D (f r*D o)-(w^2+SchwarzschildEinstein.reggeWheeler r (modeLambda m))*o := rfl
  rw [wave]
  obtain ⟨hm',hm''⟩ := mul_ne_zero_iff.mp hm
  simp [oddMasterField, reconstructAxial, oddMasterForcing, SchwarzschildEinstein.reggeWheeler, modeLambda,
    SchwarzschildEinstein.lapse, radialLapse, PureOdd.lapse, D.leibniz, D.leibniz_div,
    derivative_two, smul_eq_mul, pow_succ, dr, dm]
  field_simp [hr, hh, hm', hm'']
  ring

#print axioms sphere_of_metric
#print axioms cross_of_metric
#print axioms even_master_of_reconstruction
#print axioms axial_of_metric
#print axioms odd_master_of_reconstruction

end
end SchwarzschildEinstein.PureOdd.Master
