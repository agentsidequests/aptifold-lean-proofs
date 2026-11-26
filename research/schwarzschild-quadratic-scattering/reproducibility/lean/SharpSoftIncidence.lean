import StaticReggeWheelerPolynomial
import StaticBarrierRatio
import ExteriorInitialData
import PhysicalSoftResponse

/-! Comparison with the normalized static polynomial gives the full
angular power in the upper absorption bound. -/
namespace SchwarzschildLaurent.LinearWave

open Set Finset Polynomial SchwarzschildLaurent.Outgoing SchwarzschildMixtures.Strain

noncomputable section

private theorem static_wave_positive (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 4 ≤ r) :
    0 < staticWave n r := by
  apply lt_of_lt_of_le _ (static_wave_growth n hn hr)
  have a := static_coefficient_positive n hn (n-2) le_rfl
  positivity

theorem static_wave_jet_positive (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 4 ≤ r) :
    0 < staticWaveJet n r := by
  have r0 : 0 < r := by linarith
  have shift0 : 0 ≤ r-2 := by linarith
  have p0 : 0 < (staticEnvelope n).eval (r-2) := by
    apply lt_of_lt_of_le _ (static_envelope_leading_lower n hn _ shift0)
    exact mul_pos (static_coefficient_positive n hn _ le_rfl)
      (pow_pos (by linarith) _)
  have dp0 : 0 ≤ (staticEnvelope n).derivative.eval (r-2) := by
    unfold staticEnvelope
    rw [map_sum]
    simp only [derivative_monomial,eval_finsetSum,eval_monomial]
    apply sum_nonneg
    intro j hj
    have I : j ≤ n-2 := by have h := mem_range.mp hj; omega
    have coeff := (static_coefficient_positive n hn j I).le
    positivity
  unfold staticWaveJet
  exact mul_pos (real_lapse_positive (by linarith)) (by positivity)

private theorem real_exterior_IVP (n : ℕ) (omega y0 z0 : ℝ) :
    ∃ y z : ℝ → ℝ, y 4 = y0 ∧ z 4 = z0 ∧
      ∀ r : ℝ, 4 ≤ r →
        HasDerivAt y ((realLapse r)⁻¹*z r) r ∧
        HasDerivAt z ((realBarrier n omega r/realLapse r)*y r) r := by
  obtain ⟨Y,Z,hy,hz,derivative⟩ :=
    exterior_wave_from_initial_data (frequencyParameter omega) (angularEigenvalue n)
      (a := 4) (by norm_num) (y0:ℂ) (z0:ℂ)
  refine ⟨fun r => (Y r).re,fun r => (Z r).re,by simp [hy],by simp [hz],?_⟩
  intro r hr
  have dy := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (derivative r hr).1
  have dz := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (derivative r hr).2
  rw [← real_lapse_cast] at dy
  rw [← real_lapse_cast,← real_barrier_cast] at dz
  simp only [Function.comp_def,Complex.reCLM_apply,Complex.div_ofReal_re] at dy
  simp only [Function.comp_def,Complex.reCLM_apply,Complex.div_ofReal_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at dz
  exact ⟨dy.congr_deriv (by ring),dz.congr_deriv (by ring)⟩

private theorem wave_growth_from_static_seed (n : ℕ) (hn : 2 ≤ n) {omega : ℝ} (wo : 0 < omega)
    (w8 : omega ≤ 1/8) (d : ℝ) (d0 : 0 < d)
    (u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1)
    (rot : ℂ) (unit : ‖rot‖ = 1)
    (u0 : d*staticWave n 4 < (rot*u.value 4).re)
    (v0 : d*staticWaveJet n 4 < (rot*u.jet 4).re) :
    (d/2)*(staticCoefficient n (n-2)/2^(n-2))*(1/(2*omega))^(n+1) ≤
      ‖u.value (1/(2*omega))‖ := by
  let R : ℝ := 1/(2*omega)
  have R4 : 4 ≤ R := (le_div_iff₀ (by positivity : 0 < 2*omega)).2 (by linarith)
  have outer : omega*R = 1/2 := by dsimp only [R]; field_simp [wo.ne']
  let F := realLapse
  let V := realBarrier n 0
  let A := fun r => (F r)⁻¹
  let B := fun r => realBarrier n omega r/F r
  let S := fun r => d*staticWave n r
  let dS := fun r => d*staticWaveJet n r
  have Spos (r : ℝ) (hr : 4 ≤ r) : 0 < S r := mul_pos d0 (static_wave_positive n hn hr)
  have dSpos (r : ℝ) (hr : 4 ≤ r) : 0 < dS r := mul_pos d0 (static_wave_jet_positive n hn hr)
  have nonnegative (r : ℝ) (hr : r ∈ Icc 4 R) : 0 ≤ A r ∧ 0 ≤ B r ∧ 0 ≤ (0:ℝ) := by
    have lap := real_lapse_positive (r := r) (by linarith [hr.1])
    have cutoff := (mul_le_mul_of_nonneg_left hr.2 wo.le).trans (le_of_eq outer)
    have barrier := square_barrier_subsolution n hn wo hr.1 cutoff
    have pos : 0 ≤ realBarrier n omega r := by
      by_contra! bad
      have prod := mul_nonpos_of_nonpos_of_nonneg bad.le (sq_nonneg r)
      linarith
    exact ⟨inv_nonneg.mpr lap.le,div_nonneg pos lap.le,le_rfl⟩
  obtain ⟨y,z,ya,za,equation⟩ := real_exterior_IVP n omega (S 4) (dS 4)
  have ypos := forward_positive_pair 4 R y z A B 0 (fun r hr => (equation r hr.1).1)
    (fun r hr => by simpa only [Pi.zero_apply,add_zero] using (equation r hr.1).2)
    nonnegative (by rw [ya]; exact Spos 4 le_rfl) (by rw [za]; exact dSpos 4 le_rfl)
  let U := u.scale rot
  let Y := fun r => (U.value r).re-y r
  let Z := fun r => (U.jet r).re-z r
  have yderive (r : ℝ) (hr : r ∈ Icc 4 R) : HasDerivAt Y (A r*Z r) r := by
    have h := (real_exterior_derivatives n omega U.equation (r := r) (by linarith [hr.1])).1
    apply (h.sub (equation r hr.1).1).congr_deriv
    dsimp only [A,F,Z]
    ring
  have zderive (r : ℝ) (hr : r ∈ Icc 4 R) : HasDerivAt Z (B r*Y r+0) r := by
    have h := (real_exterior_derivatives n omega U.equation (r := r) (by linarith [hr.1])).2
    apply (h.sub (equation r hr.1).2).congr_deriv
    dsimp only [B,F,Y]
    ring
  have larger := forward_positive_pair 4 R Y Z A B 0 yderive zderive nonnegative
    (by dsimp only [Y]; rw [ya]; exact sub_pos.mpr u0)
    (by dsimp only [Z]; rw [za]; exact sub_pos.mpr v0)
  have lowerLapse (r : ℝ) (hr : r ∈ Icc 4 R) : 1/2 ≤ F r :=
    (le_div_iff₀ (by linarith [hr.1])).2 (by linarith [hr.1])
  have staticValue (r : ℝ) (hr : r ∈ Icc 4 R) : HasDerivAt S (dS r/F r) r := by
    apply ((static_wave_radial_equation n hn (r := r) (by linarith [hr.1])).1.const_mul d).congr_deriv
    dsimp only [dS,F]
    ring
  have staticJet (r : ℝ) (hr : r ∈ Icc 4 R) : HasDerivAt dS (V r*S r/F r) r := by
    apply ((static_wave_radial_equation n hn (r := r) (by linarith [hr.1])).2.const_mul d).congr_deriv
    dsimp only [S,V,F]
    ring
  have mono : MonotoneOn S (Icc 4 R) := monotone_from_nonnegative_derivative staticValue
    (fun r hr => div_nonneg (dSpos r hr.1).le (real_lapse_positive (by linarith [hr.1])).le)
  have perturbedValue (r : ℝ) (hr : r ∈ Icc 4 R) : HasDerivAt y (z r/F r) r :=
    (equation r hr.1).1.congr_deriv (by dsimp only [F]; ring)
  have perturbedJet (r : ℝ) (hr : r ∈ Icc 4 R) : HasDerivAt z ((V r-omega^2)*y r/F r) r := by
    apply (equation r hr.1).2.congr_deriv
    dsimp only [V,F,realBarrier]
    norm_num
    ring
  have comparison := static_wave_comparison 4 R omega R4 F V S dS y z lowerLapse
    (fun r hr => Spos r hr.1) mono (fun r hr => (ypos r hr).1.le) staticValue staticJet
    perturbedValue perturbedJet ya za R ⟨R4,le_rfl⟩
  have short : omega*(R-4) ≤ 1/2 := by
    rw [mul_sub,outer]
    exact sub_le_self _ (by positivity)
  have square := (sq_le_sq₀ (mul_nonneg wo.le (sub_nonneg.mpr R4)) (by norm_num : (0:ℝ) ≤ 1/2)).2 short
  have half : (1:ℝ)/2 ≤ 1-2*omega^2*(R-4)^2 := by
    rw [mul_pow] at square
    nlinarith
  have lower : S R/2 ≤ y R :=
    (by simpa only [div_eq_mul_inv,mul_comm,one_mul] using mul_le_mul_of_nonneg_right half (Spos R R4).le :
      S R/2 ≤ (1-2*omega^2*(R-4)^2)*S R).trans comparison
  have reUp := Complex.re_le_norm (rot*u.value R)
  rw [norm_mul,unit,one_mul] at reUp
  calc
    _ = (d/2)*((staticCoefficient n (n-2)/2^(n-2))*R^(n+1)) := by dsimp only [R]; ring
    _ ≤ S R/2 := by
      dsimp only [S]
      have h := mul_le_mul_of_nonneg_left (static_wave_growth n hn R4) (by positivity : 0 ≤ d/2)
      linarith
    _ ≤ y R := lower
    _ ≤ _ := (sub_pos.mp (larger R ⟨R4,le_rfl⟩).1).le.trans reUp

theorem sharp_unit_horizon_incidence (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : ℝ, 0 < A ∧ ∀ {omega : ℝ}, 0 < omega →
      omega ≤ 1/(24*(100+4*((n:ℝ)*(n+1)))) →
      ∀ u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1,
        A/omega^(n+1) ≤ ‖u.incoming‖ := by
  let L : ℝ := (n:ℝ)*(n+1)
  let c := horizonSeedDistance L/100
  let d := c/(1+staticWave n 4+staticWaveJet n 4)
  let B := staticCoefficient n (n-2)/2^(n-2)
  have s0 := static_wave_positive n hn (r := 4) le_rfl
  have z0 := static_wave_jet_positive n hn (r := 4) le_rfl
  have c0 : 0 < c := by
    have p := (horizon_seed_distance_properties (show 0 ≤ L by dsimp [L]; positivity)).2.1
    exact div_pos p (by norm_num)
  have d0 : 0 < d := by dsimp only [d]; positivity
  have B0 : 0 < B := div_pos (static_coefficient_positive n hn _ le_rfl) (by positivity)
  let A := (d*B/(4*2^(n+1)))*Real.exp (-2*(L+3))
  refine ⟨A,by dsimp only [A]; positivity,?_⟩
  intro omega wo small u
  have w8 : omega ≤ 1/8 := small.trans
    ((div_le_iff₀ (by positivity : 0 < 24*(100+4*L))).2 (by linarith [show 0 ≤ L by positivity]))
  obtain ⟨rot,unit,first,second⟩ := positive_four_mass_seeds n hn wo small u
  let denom := 1+staticWave n 4+staticWaveJet n 4
  have p0 : 0 < denom := by dsimp only [denom]; positivity
  have s : d*staticWave n 4 ≤ c := by
    change c/denom*staticWave n 4 ≤ c
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ p0).2 (mul_le_mul_of_nonneg_left (by dsimp only [denom]; linarith) c0.le)
  have t : d*staticWaveJet n 4 ≤ c := by
    change c/denom*staticWaveJet n 4 ≤ c
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ p0).2 (mul_le_mul_of_nonneg_left (by dsimp only [denom]; linarith) c0.le)
  change c*4^2 < (rot*u.value 4).re at first
  change 4*c < (rot*u.jet 4).re at second
  have grow := wave_growth_from_static_seed n hn wo w8 d d0 u rot unit
    (s.trans_lt (by linarith)) (t.trans_lt (by linarith))
  have readout := soft_incidence_at_matching_radius n wo w8 u
  calc
    _ = (((d/2)*B*(1/(2*omega))^(n+1))/2)*Real.exp (-2*(L+3)) := by
      dsimp only [A]
      rw [div_pow,one_pow,mul_pow]
      field_simp [wo.ne']
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right grow (by norm_num))
      (Real.exp_pos _).le).trans readout

theorem sharp_unit_horizon_absorption (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {omega : ℝ}, 0 < omega →
      omega ≤ 1/(24*(100+4*((n:ℝ)*(n+1)))) →
      ∀ u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1,
        1-‖u.outgoing/u.incoming‖^2 ≤ C*omega^(2*n+2) := by
  obtain ⟨A,A0,lower⟩ := sharp_unit_horizon_incidence n hn
  refine ⟨1/A^2,by positivity,?_⟩
  intro omega wo small u
  have k0 : frequencyParameter omega ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr wo.ne') Complex.I_ne_zero
  have ki : (frequencyParameter omega).re = 0 := by simp [frequencyParameter]
  have b0 : 0 < A/omega^(n+1) := div_pos A0 (by positivity)
  have a := lower wo small u
  have power := (sq_le_sq₀ b0.le (norm_nonneg _)).2 a
  rw [unit_horizon_reflected_fraction _ n k0 ki u]
  calc
    _ = 1/‖u.incoming‖^2 := by ring
    _ ≤ 1/(A/omega^(n+1))^2 := one_div_le_one_div_of_le (by positivity) power
    _ = _ := by
      rw [show 2*n+2 = (n+1)*2 by omega,pow_mul]
      field_simp [A0.ne',wo.ne']

#print axioms static_wave_jet_positive
#print axioms sharp_unit_horizon_incidence
#print axioms sharp_unit_horizon_absorption

end
end SchwarzschildLaurent.LinearWave
