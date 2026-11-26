import ParityReconstructionConservation

/-! Conservation completes the sourced equations after the
reconstruction has matched the independent constraint readouts. -/
namespace SchwarzschildEinstein.PureOdd.Master

noncomputable section
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
variable (D : Derivation ℚ K K)

local notation "f" => radialLapse

def zeroMode : ModeSource K := ⟨⟨0,0,0,0,0⟩,0,0,⟨0,0⟩,0⟩

omit [CharZero K] [Algebra ℚ K] in
theorem source_difference_eq_zero (a b : ModeSource K) :
    sourceDifference a b = zeroMode ↔ a = b := by
  obtain ⟨⟨att,arr,arv,ast,atf⟩,atr,atv,⟨atm,ar⟩,ash⟩ := a
  obtain ⟨⟨btt,brr,brv,bst,btf⟩,btr,btv,⟨bt,br⟩,bsh⟩ := b
  simp [sourceDifference, polarDifference, zeroMode, sub_eq_zero]

theorem even_forcing_difference (r m : K) (a b : EvenSource K) :
    evenMasterForcing D r m (polarDifference a b) =
      evenMasterForcing D r m a - evenMasterForcing D r m b := by
  have trace : orbitHalfTrace r (polarDifference a b) = orbitHalfTrace r a - orbitHalfTrace r b := by
    simp only [orbitHalfTrace, polarDifference]
    ring
  unfold evenMasterForcing
  simp only [trace, map_sub]
  simp only [polarDifference]
  ring

private theorem radial_force_relation (r w m : K) (s : ModeSource K) (hr : r ≠ 0)
    (hl : m*(m+1) ≠ 0) (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1)
    (tt : s.polar.tt = 0) (tr : s.tr = 0) (tf : s.polar.traceFree = 0) :
    let p := modeLambda m*r+3
    evenMasterForcing D r m s.polar =
      2*r*(f r)^2/p*(s.polar.radialVector+r/2*s.polar.rr) -
        2*r^3*(f r)^2/(m*(m+1)*p)*radiusBalance D r w m s := by
  simp [evenMasterForcing, orbitHalfTrace, radiusBalance, tt, tr, tf, radialLapse, PureOdd.lapse,
    D.leibniz, D.leibniz_div, derivative_two, smul_eq_mul, pow_succ, dr]
  obtain ⟨hm,hm'⟩ := mul_ne_zero_iff.mp hl
  generalize pole_eq : modeLambda m*r+3 = pole at hp ⊢
  field_simp [hr, hm, hm', hp]
  subst pole
  unfold modeLambda
  ring

private theorem radial_polar_relation (r w m : K) (s : ModeSource K)
    (hr : r ≠ 0) (dr : D r = 1)
    (tt : s.polar.tt = 0) (tr : s.tr = 0) (tf : s.polar.traceFree = 0)
    (t : s.timeVector = 0) (v : s.polar.radialVector = -(r/2*s.polar.rr)) :
    radiusBalance D r w m s+2/r*polarBalance D r w m s =
      (modeLambda m*r+3)/r^2*s.polar.rr := by
  simp [radiusBalance, polarBalance, vectorDivergence, tt, tr, tf, t, v,
    radialLapse, PureOdd.lapse, modeLambda, D.leibniz, D.leibniz_div, derivative_two,
    smul_eq_mul, dr]
  field_simp [hr]
  ring

theorem conserved_residual_zero (r w m : K) (s : ModeSource K)
    (hr : r ≠ 0) (hf : f r ≠ 0) (hl : m*(m+1) ≠ 0) (hmu : (m-1)*(m+2) ≠ 0)
    (hp : modeLambda m*r+3 ≠ 0) (dr : D r = 1) (hc : ConservedMode D r w m s)
    (tt : s.polar.tt = 0) (tr : s.tr = 0) (tf : s.polar.traceFree = 0)
    (atime : s.axial.time = 0) (arad : s.axial.radius = 0)
    (forcing : evenMasterForcing D r m s.polar = 0) :
    s = zeroMode := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  have hrr : r^2 ≠ 0 := pow_ne_zero 2 hr
  have t : s.timeVector = 0 := by
    have eq : -(m*(m+1)/r^2*s.timeVector) = 0 := by
      simpa only [timeBalance, tt, tr, map_zero, mul_zero, zero_add, sub_eq_neg_add, add_zero] using hc.time
    exact (mul_eq_zero.mp (neg_eq_zero.mp eq)).resolve_left (div_ne_zero hl hrr)
  have v : s.polar.radialVector = -(r/2*s.polar.rr) := by
    have eq := radial_force_relation D r w m s hr hl hp dr tt tr tf
    simp only [forcing, hc.radius, mul_zero, sub_zero] at eq
    have nz : 2*r*(f r)^2/(modeLambda m*r+3) ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero h2 hr) (pow_ne_zero 2 hf)) hp
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp eq.symm).resolve_left nz)
  have rr : s.polar.rr = 0 := by
    have eq := radial_polar_relation D r w m s hr dr tt tr tf t v
    rw [hc.radius, hc.polar, mul_zero, add_zero] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_left (div_ne_zero hp hrr)
  have zv : s.polar.radialVector = 0 := by rw [v, rr, mul_zero, neg_zero]
  have trace : s.polar.sphereTrace = 0 := by
    have eq : s.polar.sphereTrace/r^2 = 0 := by
      simpa [polarBalance, vectorDivergence, tf, t, zv] using hc.polar
    exact (div_eq_zero_iff.mp eq).resolve_right hrr
  have aTensor : s.axialTensor = 0 := by
    have eq : -((m-1)*(m+2)/(2*r^2)*s.axialTensor) = 0 := by
      simpa [axialBalance, vectorDivergence, atime, arad] using hc.axial
    exact (mul_eq_zero.mp (neg_eq_zero.mp eq)).resolve_left
      (div_ne_zero hmu (mul_ne_zero h2 hrr))
  obtain ⟨⟨stt,srr,srv,sst,stf⟩,str,stv,⟨sat,sar⟩,ssh⟩ := s
  simp_all [zeroMode]

#print axioms source_difference_eq_zero
#print axioms even_forcing_difference
#print axioms conserved_residual_zero

end
end SchwarzschildEinstein.PureOdd.Master
