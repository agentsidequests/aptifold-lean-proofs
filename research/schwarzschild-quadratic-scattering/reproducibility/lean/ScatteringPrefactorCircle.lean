import OutgoingStrainNormalization

/-! The ratio of the two complex prefactors in the second scattering
formula. Reflection amplitudes enter only after the prefactor analysis. -/
namespace SchwarzschildMixtures.Strain

open SchwarzschildLaurent.Outgoing

noncomputable section

def parentRate (n : ℕ) : ℝ :=
  ((n : ℝ)-1)*n*(n+1)*(n+2)/12

def daughterRate (n : ℕ) : ℝ := parentRate (2*n)/2

def prefactorRatio (g G : ℝ) (k : ℂ) : ℂ :=
  (k-(g:ℂ)^2/(G:ℂ))*(k-(G:ℂ))/(k+(g:ℂ))^2

def prefactorCircleRadius (g G : ℝ) : ℝ := (G+g)^2/(4*G*g)

def secondResponsePrefactor (n : ℕ) (k : ℂ) : ℂ :=
  (printedScale n : ℂ)/(4*(daughterRate n : ℂ))*(k/(k-(daughterRate n : ℂ)))

theorem parent_rate_cast (n : ℕ) : (parentRate n : ℂ) = gamma (n : ℂ) := by
  simp [parentRate,gamma]

private theorem daughter_rate_cast (n : ℕ) : (daughterRate n : ℂ) = daughterGamma (n : ℂ) := by
  simp [daughterRate,daughterGamma,parent_rate_cast,Nat.cast_mul]

theorem parent_rate_positive (n : ℕ) (hn : 2 ≤ n) : 0 < parentRate n := by
  simpa only [← parent_rate_cast n,Complex.ofReal_re] using gamma_positive n hn

theorem daughter_rate_gt_parent (n : ℕ) (hn : 2 ≤ n) : parentRate n < daughterRate n := by
  have gap := gap_positive n hn
  rw [← parent_rate_cast,← daughter_rate_cast,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_re] at gap
  linarith

private theorem real_shift_nonzero (k : ℂ) (ki : k.re = 0) (a : ℝ) (ha : a ≠ 0) :
    k+(a:ℂ) ≠ 0 := by
  intro zero
  apply ha
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.zero_re,ki,zero_add] using congrArg Complex.re zero

private theorem square_norm_shift (k : ℂ) (ki : k.re = 0) (a : ℝ) :
    ‖k+(a:ℂ)‖^2 = k.im^2+a^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,ki,zero_add,add_zero]
  ring

private theorem square_norm_sub (k : ℂ) (ki : k.re = 0) (a : ℝ) :
    ‖k-(a:ℂ)‖^2 = k.im^2+a^2 := by
  simpa [sub_eq_add_neg] using square_norm_shift k ki (-a)

theorem prefactor_circle (g G : ℝ) (hg : 0 < g) (hG : 0 < G) (k : ℂ) (ki : k.re = 0) :
    prefactorRatio g G k =
      (1-(prefactorCircleRadius g G : ℂ))+
        (prefactorCircleRadius g G : ℂ)*((k-(g:ℂ))/(k+(g:ℂ)))^2 := by
  have g0 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have G0 : (G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have denom := real_shift_nonzero k ki g hg.ne'
  unfold prefactorRatio prefactorCircleRadius
  push_cast
  field_simp [g0,G0,denom]
  ring

theorem prefactor_circle_parameter_unit (g : ℝ) (hg : 0 < g) (k : ℂ) (ki : k.re = 0) :
    ‖(k-(g:ℂ))/(k+(g:ℂ))‖ = 1 := by
  have same : ‖k-(g:ℂ)‖ = ‖k+(g:ℂ)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [square_norm_sub k ki,square_norm_shift k ki]
  rw [norm_div,same,div_self (norm_ne_zero_iff.mpr (real_shift_nonzero k ki g hg.ne'))]

theorem prefactor_square_norm (g G : ℝ) (hg : 0 < g) (hG : 0 < G) (k : ℂ) (ki : k.re = 0) :
    ‖prefactorRatio g G k‖^2 =
      1+k.im^2*(G^2-g^2)^2/(G^2*(k.im^2+g^2)^2) := by
  have cast : (↑(g^2/G) : ℂ) = (g:ℂ)^2/(G:ℂ) := by push_cast; rfl
  have d : 0 < k.im^2+g^2 := by positivity
  calc
    _ = (k.im^2+(g^2/G)^2)*(k.im^2+G^2)/(k.im^2+g^2)^2 := by
      simp only [prefactorRatio,← cast,norm_div,norm_mul,norm_pow,div_pow,mul_pow,
        square_norm_sub k ki,square_norm_shift k ki]
    _ = _ := by
      field_simp [hG.ne',d.ne']
      ring

theorem prefactor_peak_gap (g G : ℝ) (hg : 0 < g) (hG : 0 < G) (k : ℂ) (ki : k.re = 0) :
    ((G^2+g^2)/(2*G*g))^2-‖prefactorRatio g G k‖^2 =
      (G^2-g^2)^2*(k.im^2-g^2)^2/(4*G^2*g^2*(k.im^2+g^2)^2) := by
  have d : 0 < k.im^2+g^2 := by positivity
  rw [prefactor_square_norm g G hg hG k ki]
  field_simp [hg.ne',hG.ne',d.ne']
  ring

theorem prefactor_modulus_bounds (g G : ℝ) (hg : 0 < g) (gap : g < G)
    (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    1 < ‖prefactorRatio g G k‖ ∧ ‖prefactorRatio g G k‖ ≤ (G^2+g^2)/(2*G*g) := by
  have hG := hg.trans gap
  constructor
  · apply (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 1) (norm_nonneg _)).mp
    rw [one_pow,prefactor_square_norm g G hg hG k ki]
    have nonzero : k.im ≠ 0 := fun h => hk (by apply Complex.ext <;> simp [ki,h])
    have square : g^2 < G^2 := (sq_lt_sq₀ hg.le hG.le).2 gap
    have extra : 0 < k.im^2*(G^2-g^2)^2/(G^2*(k.im^2+g^2)^2) :=
      div_pos (mul_pos (sq_pos_of_ne_zero nonzero) (sq_pos_of_pos (sub_pos.mpr square))) (by positivity)
    linarith
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    apply sub_nonneg.mp
    rw [prefactor_peak_gap g G hg hG k ki]
    positivity

theorem prefactor_peak_attained (g G : ℝ) (hg : 0 < g) (hG : 0 < G)
    (k : ℂ) (ki : k.re = 0) (peak : k.im^2 = g^2) :
    ‖prefactorRatio g G k‖ = (G^2+g^2)/(2*G*g) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  symm
  apply sub_eq_zero.mp
  rw [prefactor_peak_gap g G hg hG k ki,peak,sub_self]
  simp

theorem printed_second_response_factored (n : ℕ) (hn : 2 ≤ n)
    (k rp rd : ℂ) (ki : k.re = 0) :
    printedResponse true k n rp rd =
      secondResponsePrefactor n k*
        (prefactorRatio (parentRate n) (daughterRate n) k*rp^2+rd) := by
  have hg := parent_rate_positive n hn
  have hG := hg.trans (daughter_rate_gt_parent n hn)
  have G0 : (daughterRate n : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have p : k+(parentRate n : ℂ) ≠ 0 := real_shift_nonzero k ki _ hg.ne'
  have m : k-(daughterRate n : ℂ) ≠ 0 := by
    rw [daughter_rate_cast]
    exact frequency_sub_daughter n hn k ki
  simp only [printedResponse,prefactorRatio,secondResponsePrefactor,
    ← parent_rate_cast n,← daughter_rate_cast n,if_true]
  field_simp [G0,p,m]

theorem printed_scale_positive (n : ℕ) (hn : 2 ≤ n) : 0 < printedScale n := by
  have lower : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have nz : (0:ℝ) ≤ (n:ℝ) := by positivity
  have squared := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 2) nz).2 lower
  have cubic : 0 < angularCubic (n:ℝ) := by
    unfold angularCubic
    norm_num at squared
    nlinarith [pow_nonneg nz 3]
  unfold printedScale
  positivity

theorem second_response_prefactor_nonzero (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    secondResponsePrefactor n k ≠ 0 := by
  have hG := (parent_rate_positive n hn).trans (daughter_rate_gt_parent n hn)
  have G0 : (daughterRate n : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have scale : (printedScale n : ℂ) ≠ 0 := by exact_mod_cast (printed_scale_positive n hn).ne'
  have minus : k-(daughterRate n : ℂ) ≠ 0 := by
    rw [daughter_rate_cast]
    exact frequency_sub_daughter n hn k ki
  exact mul_ne_zero (div_ne_zero scale (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) G0))
    (div_ne_zero hk minus)

theorem printed_second_zero_iff (n : ℕ) (hn : 2 ≤ n) (k rp rd : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    printedResponse true k n rp rd = 0 ↔
      rd = -prefactorRatio (parentRate n) (daughterRate n) k*rp^2 := by
  have nonzero := second_response_prefactor_nonzero n hn k hk ki
  rw [printed_second_response_factored n hn k rp rd ki,mul_eq_zero]
  simp only [nonzero,false_or]
  constructor
  · intro sum
    linear_combination sum
  · intro eq
    linear_combination eq

/-- Mismatch in term magnitudes bounds the strain for every relative phase. -/
theorem printed_second_magnitude_floor (n : ℕ) (hn : 2 ≤ n) (k rp rd : ℂ) (ki : k.re = 0) :
    ‖secondResponsePrefactor n k‖*
      (‖prefactorRatio (parentRate n) (daughterRate n) k‖*‖rp‖^2-‖rd‖) ≤
      ‖printedResponse true k n rp rd‖ := by
  rw [printed_second_response_factored n hn k rp rd ki,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have h := norm_sub_norm_le (prefactorRatio (parentRate n) (daughterRate n) k*rp^2) (-rd)
  rwa [norm_mul,norm_pow,norm_neg,sub_neg_eq_add] at h

theorem printed_second_nonzero_of_reflection (n : ℕ) (hn : 2 ≤ n)
    (k rp rd : ℂ) (hk : k ≠ 0) (ki : k.re = 0)
    (daughter : ‖rd‖ ≤ 1)
    (parent : 1 < ‖prefactorRatio (parentRate n) (daughterRate n) k‖*‖rp‖^2) :
    printedResponse true k n rp rd ≠ 0 := by
  intro zero
  rw [(printed_second_zero_iff n hn k rp rd hk ki).1 zero,norm_mul,norm_neg,norm_pow] at daughter
  exact (not_le_of_gt parent) daughter

#print axioms prefactor_circle
#print axioms prefactor_circle_parameter_unit
#print axioms prefactor_square_norm
#print axioms prefactor_peak_gap
#print axioms prefactor_modulus_bounds
#print axioms prefactor_peak_attained
#print axioms printed_second_response_factored
#print axioms second_response_prefactor_nonzero
#print axioms printed_second_zero_iff
#print axioms printed_second_magnitude_floor
#print axioms printed_second_nonzero_of_reflection

end
end SchwarzschildMixtures.Strain
