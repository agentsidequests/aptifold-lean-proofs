import LinearLowFrequencyBarrier

/-! Comparison with a static growing wave on a finite exterior interval.
The derivative equations are written in areal radius, while J is the
static-square weighted tortoise derivative. -/
namespace SchwarzschildLaurent.LinearWave

open Set

noncomputable section

/-- The ratio to a positive increasing static wave loses at most
(2\omega^2(r-a)^2) when the initial weighted derivative vanishes.
The interval only needs a lapse bounded below by (1/2). -/
theorem static_comparison_ratio_lower (a b omega : ℝ) (ab : a ≤ b) (U q J F : ℝ → ℝ)
    (static_pos : ∀ r ∈ Icc a b, 0 < U r) (static_mono : MonotoneOn U (Icc a b))
    (ratio_nonneg : ∀ r ∈ Icc a b, 0 ≤ q r)
    (lapse : ∀ r ∈ Icc a b, (1:ℝ)/2 ≤ F r)
    (dq : ∀ r ∈ Icc a b, HasDerivAt q (J r/(F r*U r^2)) r)
    (dJ : ∀ r ∈ Icc a b, HasDerivAt J (-(omega^2*U r^2*q r/F r)) r)
    (initial_q : q a = 1) (initial_J : J a = 0) :
    ∀ r ∈ Icc a b, 1-2*omega^2*(r-a)^2 ≤ q r := by
  have ha : a ∈ Icc a b := ⟨le_rfl,ab⟩
  have fpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < F r := (by norm_num : (0:ℝ) < 1/2).trans_le (lapse r hr)
  have negJmono : MonotoneOn (fun r => -J r) (Icc a b) := by
    apply monotone_from_nonnegative_derivative
      (df := fun r => omega^2*U r^2*q r/F r)
    · intro r hr
      change HasDerivAt (-J) _ r
      simpa only [neg_neg] using (dJ r hr).neg
    · intro r hr
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (ratio_nonneg r hr)) (fpos r hr).le
  have J_nonpos (r : ℝ) (hr : r ∈ Icc a b) : J r ≤ 0 := by
    have bound := negJmono ha hr hr.1
    simpa only [initial_J,neg_zero,neg_nonneg] using bound
  have negqmono : MonotoneOn (fun r => -q r) (Icc a b) := by
    apply monotone_from_nonnegative_derivative
      (df := fun r => (-J r)/(F r*U r^2))
    · intro r hr
      change HasDerivAt (-q) _ r
      simpa only [neg_div] using (dq r hr).neg
    · intro r hr
      exact div_nonneg (neg_nonneg.mpr (J_nonpos r hr))
        (mul_nonneg (fpos r hr).le (sq_nonneg _))
  have q_le_one (r : ℝ) (hr : r ∈ Icc a b) : q r ≤ 1 := by
    have bound := negqmono ha hr hr.1
    simpa only [initial_q,neg_le_neg_iff] using bound
  have Jlower (r : ℝ) (hr : r ∈ Icc a b) : -2*omega^2*(U r)^2*(r-a) ≤ J r := by
    let K := 2*omega^2*(U r)^2
    let extend := fun s : ℝ => J s+K*(s-a)
    have belongs {s : ℝ} (hs : s ∈ Icc a r) : s ∈ Icc a b := ⟨hs.1,hs.2.trans hr.2⟩
    have mono : MonotoneOn extend (Icc a r) := by
      apply monotone_from_nonnegative_derivative
        (df := fun s => -(omega^2*U s^2*q s/F s)+K)
      · intro s hs
        change HasDerivAt (J + fun t => K*(id t-a)) _ s
        simpa only [extend,mul_one] using
          (dJ s (belongs hs)).add (((hasDerivAt_id s).sub_const a).const_mul K)
      · intro s hs
        have castS := belongs hs
        have boundU := pow_le_pow_left₀ (static_pos s castS).le (static_mono castS hr hs.2) 2
        have numerator : omega^2*U s^2*q s ≤ omega^2*(U r)^2 := by
          calc
            _ = omega^2*(U s^2*q s) := by ring
            _ ≤ omega^2*((U r)^2*1) := mul_le_mul_of_nonneg_left
              (mul_le_mul boundU (q_le_one s castS) (ratio_nonneg s castS) (sq_nonneg _)) (sq_nonneg _)
            _ = _ := by rw [mul_one]
        have weighted : omega^2*U s^2*q s/F s ≤ K := by
          apply (div_le_iff₀ (fpos s castS)).2
          calc
            _ ≤ omega^2*(U r)^2 := numerator
            _ = K*(1/2) := by dsimp only [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (lapse s castS) (by dsimp only [K]; positivity)
        linarith
    have bound := mono ⟨le_rfl,hr.1⟩ ⟨hr.1,le_rfl⟩ hr.1
    simp only [extend,initial_J,sub_self,mul_zero,add_zero] at bound
    dsimp only [K] at bound
    linarith
  have qSlope (r : ℝ) (hr : r ∈ Icc a b) : -4*omega^2*(r-a) ≤ J r/(F r*U r^2) := by
    have product : 0 < F r*U r^2 := mul_pos (fpos r hr) (sq_pos_of_pos (static_pos r hr))
    have twice : (2:ℝ) ≤ 4*F r := by linarith [lapse r hr]
    have factor : 0 ≤ omega^2*(r-a)*U r^2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hr.1)) (sq_nonneg _)
    apply (le_div_iff₀ product).2
    calc
      _ = -(4*F r)*(omega^2*(r-a)*U r^2) := by ring
      _ ≤ (-2:ℝ)*(omega^2*(r-a)*U r^2) := mul_le_mul_of_nonneg_right (neg_le_neg twice) factor
      _ = -2*omega^2*(U r)^2*(r-a) := by ring
      _ ≤ J r := Jlower r hr
  let above := fun r : ℝ => q r+2*omega^2*(r-a)^2
  have monotone : MonotoneOn above (Icc a b) := by
    apply monotone_from_nonnegative_derivative
      (df := fun r => J r/(F r*U r^2)+4*omega^2*(r-a))
    · intro r hr
      have parabola := (((hasDerivAt_id r).sub_const a).pow 2).const_mul (2*omega^2)
      apply ((dq r hr).add parabola).congr_deriv
      dsimp only [id_eq]
      ring
    · intro r hr
      linarith [qSlope r hr]
  intro r hr
  have bound := monotone ha hr hr.1
  simp only [above,initial_q,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero] at bound
  linarith

/-- Apply the comparison to two actual differential equations on the
same interval. The static and perturbed waves start with equal data. -/
theorem static_wave_comparison (a b omega : ℝ) (ab : a ≤ b) (F V U dU Y dY : ℝ → ℝ)
    (lapse : ∀ r ∈ Icc a b, (1:ℝ)/2 ≤ F r)
    (static_pos : ∀ r ∈ Icc a b, 0 < U r) (static_mono : MonotoneOn U (Icc a b))
    (perturbed_nonneg : ∀ r ∈ Icc a b, 0 ≤ Y r)
    (static_value : ∀ r ∈ Icc a b, HasDerivAt U (dU r/F r) r)
    (static_jet : ∀ r ∈ Icc a b, HasDerivAt dU (V r*U r/F r) r)
    (perturbed_value : ∀ r ∈ Icc a b, HasDerivAt Y (dY r/F r) r)
    (perturbed_jet : ∀ r ∈ Icc a b, HasDerivAt dY ((V r-omega^2)*Y r/F r) r)
    (initial_value : Y a = U a) (initial_jet : dY a = dU a) :
    ∀ r ∈ Icc a b, (1-2*omega^2*(r-a)^2)*U r ≤ Y r := by
  let ratio := fun r => Y r/U r
  let J := fun r => U r*dY r-Y r*dU r
  have fpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < F r := (by norm_num : (0:ℝ) < 1/2).trans_le (lapse r hr)
  have ratio_nonneg (r : ℝ) (hr : r ∈ Icc a b) : 0 ≤ ratio r :=
    div_nonneg (perturbed_nonneg r hr) (static_pos r hr).le
  have ratio_derivative (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt ratio (J r/(F r*U r^2)) r := by
    apply ((perturbed_value r hr).div (static_value r hr) (static_pos r hr).ne').congr_deriv
    dsimp only [J]
    field_simp [(fpos r hr).ne',(static_pos r hr).ne']
  have J_derivative (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt J (-(omega^2*U r^2*ratio r/F r)) r := by
    apply (((static_value r hr).mul (perturbed_jet r hr)).sub
      ((perturbed_value r hr).mul (static_jet r hr))).congr_deriv
    dsimp only [ratio]
    field_simp [(fpos r hr).ne',(static_pos r hr).ne']
    ring
  have q0 : ratio a = 1 := by
    dsimp only [ratio]
    rw [initial_value,div_self (static_pos a ⟨le_rfl,ab⟩).ne']
  have J0 : J a = 0 := by
    dsimp only [J]
    rw [initial_value,initial_jet,sub_self]
  intro r hr
  exact (le_div_iff₀ (static_pos r hr)).mp
    (static_comparison_ratio_lower a b omega ab U ratio J F static_pos static_mono ratio_nonneg
      lapse ratio_derivative J_derivative q0 J0 r hr)

#print axioms static_comparison_ratio_lower
#print axioms static_wave_comparison

end
end SchwarzschildLaurent.LinearWave
