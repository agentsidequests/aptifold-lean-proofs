import ScatteringPrefactorCircle

/-! The low-frequency magnitude obstruction to exact cancellation.
The only asymptotic scattering input is parent reflection loss
small compared with the frequency squared. -/
namespace SchwarzschildMixtures.Strain

open Filter Set SchwarzschildLaurent.Outgoing
open scoped Topology

noncomputable section

def frequencyParameter (omega : ℝ) : ℂ := (omega : ℂ)*Complex.I

private theorem frequency_parameter_real_part (omega : ℝ) : (frequencyParameter omega).re = 0 := by
  simp [frequencyParameter,Complex.mul_re]

private theorem frequency_parameter_imag_part (omega : ℝ) : (frequencyParameter omega).im = omega := by
  simp [frequencyParameter,Complex.mul_im]

theorem frequency_parameter_limit :
    Tendsto frequencyParameter (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto (fun omega : ℝ => omega) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  change Tendsto (fun omega : ℝ => (omega:ℂ)*Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul] using
    ((Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.comp h).mul_const Complex.I

private theorem prefactor_modulus_limit (g G : ℝ) (hg : 0 < g) (hG : 0 < G) :
    Tendsto (fun omega => ‖prefactorRatio g G (frequencyParameter omega)‖) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have g0 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have G0 : (G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have at_zero : prefactorRatio g G 0 = 1 := by
    unfold prefactorRatio
    field_simp [g0,G0]
    ring
  have continuous : ContinuousAt (prefactorRatio g G) 0 := by
    unfold prefactorRatio
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa only [zero_add] using pow_ne_zero 2 g0
  have limit := (continuous.tendsto.comp frequency_parameter_limit).norm
  simpa only [Function.comp_def,at_zero,norm_one] using limit

private theorem scaled_excess (g G : ℝ) (hg : 0 < g) (hG : 0 < G) {omega : ℝ} (ne : omega ≠ 0) :
    (‖prefactorRatio g G (frequencyParameter omega)‖-1)/omega^2 =
      (G^2-g^2)^2/(G^2*(omega^2+g^2)^2*(‖prefactorRatio g G (frequencyParameter omega)‖+1)) := by
  let M := ‖prefactorRatio g G (frequencyParameter omega)‖
  let d := G^2*(omega^2+g^2)^2
  have denom : 0 < d := by dsimp only [d]; positivity
  have square : M^2 = 1+omega^2*(G^2-g^2)^2/d := by
    simpa only [M,d,frequency_parameter_imag_part] using
      prefactor_square_norm g G hg hG (frequencyParameter omega) (frequency_parameter_real_part omega)
  have relation : (M-1)*(M+1) = omega^2*(G^2-g^2)^2/d := by
    calc
      _ = M^2-1 := by ring
      _ = _ := by rw [square]; ring
  change (M-1)/omega^2 = (G^2-g^2)^2/(d*(M+1))
  apply (div_eq_div_iff (pow_ne_zero 2 ne) (by dsimp only [M]; positivity)).2
  calc
    _ = (M-1)*(M+1)*d := by ring
    _ = (omega^2*(G^2-g^2)^2/d)*d := by rw [relation]
    _ = _ := by rw [div_mul_cancel₀ _ denom.ne']; ring

theorem prefactor_scaled_excess_limit (g G : ℝ) (hg : 0 < g) (hG : 0 < G) :
    Tendsto (fun omega => (‖prefactorRatio g G (frequencyParameter omega)‖-1)/omega^2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((G^2-g^2)^2/(2*G^2*g^4))) := by
  have freq : Tendsto (fun omega : ℝ => omega) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have eps := prefactor_modulus_limit g G hg hG
  have d := ((((freq.pow 2).add_const (g^2)).pow 2).const_mul (G^2)).mul (eps.add_const 1)
  have c : G^2*(0^2+g^2)^2*(1+1) = 2*G^2*g^4 := by ring
  rw [c] at d
  have lim := (tendsto_const_nhds (x := (G^2-g^2)^2)).div d (by positivity)
  apply lim.congr'
  filter_upwards [self_mem_nhdsWithin] with omega pos
  exact (scaled_excess g G hg hG (show 0 < omega from pos).ne').symm

theorem second_prefactor_scaled_limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun omega => ‖secondResponsePrefactor n (frequencyParameter omega)‖/omega)
      (𝓝[>] (0 : ℝ)) (𝓝 (printedScale n/(4*daughterRate n^2))) := by
  let G := daughterRate n
  let K := printedScale n
  have hG : 0 < G := (parent_rate_positive n hn).trans (daughter_rate_gt_parent n hn)
  have hK : 0 < K := printed_scale_positive n hn
  have shift : Tendsto (fun omega => ‖frequencyParameter omega-(G:ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 G) := by
    simpa only [zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hG] using
      (frequency_parameter_limit.sub_const (G:ℂ)).norm
  have result := (tendsto_const_nhds (x := K)).div (shift.const_mul (4*G)) (by positivity)
  have value : K/(4*G*G) = K/(4*G^2) := by rw [pow_two]; congr 1; ring
  rw [value] at result
  apply result.congr'
  filter_upwards [self_mem_nhdsWithin] with omega pos0
  have pos : 0 < omega := pos0
  have absfreq : ‖frequencyParameter omega‖ = omega := by
    simp [frequencyParameter,Complex.norm_real,abs_of_pos pos]
  have nz : ‖frequencyParameter omega-(G:ℂ)‖ ≠ 0 := by
    apply norm_ne_zero_iff.2
    intro z
    have zreal := congrArg Complex.re z
    simp only [Complex.sub_re,frequency_parameter_real_part,Complex.ofReal_re,Complex.zero_re,zero_sub] at zreal
    linarith
  change K/(4*G*‖frequencyParameter omega-(G:ℂ)‖) =
    ‖(K:ℂ)/(4*(G:ℂ))*(frequencyParameter omega/(frequencyParameter omega-(G:ℂ)))‖/omega
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat,
    abs_of_pos hK,abs_of_pos hG,absfreq]
  field_simp [pos.ne',hG.ne',nz]

/-- A uniform upper bound on parent reflection loss gives the same
cubic strain floor for all allowed complex reflection coefficients. -/
theorem second_response_soft_floor_of_loss_bound (n : ℕ) (hn : 2 ≤ n) (lossBound : ℝ → ℝ)
    (loss : Tendsto (fun omega => lossBound omega/omega^2) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ omega in 𝓝[>] (0 : ℝ),
      ∀ rp rd : ℂ, 1-‖rp‖^2 ≤ lossBound omega → ‖rd‖ ≤ 1 →
        c*omega^3 ≤ ‖printedResponse true (frequencyParameter omega) n rp rd‖ := by
  let g := parentRate n
  let G := daughterRate n
  let M := fun omega : ℝ => ‖prefactorRatio g G (frequencyParameter omega)‖
  let a := (G^2-g^2)^2/(2*G^2*g^4)
  let b := printedScale n/(4*G^2)
  have hg : 0 < g := parent_rate_positive n hn
  have gap : g < G := daughter_rate_gt_parent n hn
  have hG := hg.trans gap
  have ha : 0 < a := by
    have sq := (sq_lt_sq₀ hg.le hG.le).2 gap
    unfold a
    exact div_pos (sq_pos_of_pos (sub_pos.mpr sq)) (by positivity)
  have hb : 0 < b := div_pos (printed_scale_positive n hn) (by positivity)
  have main : Tendsto (fun omega => (M omega*(1-lossBound omega)-1)/omega^2) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have lim := (prefactor_scaled_excess_limit g G hg hG).sub ((prefactor_modulus_limit g G hg hG).mul loss)
    simp only [mul_zero,sub_zero] at lim
    apply lim.congr
    intro omega
    dsimp only [M]
    ring
  have pref := second_prefactor_scaled_limit n hn
  have lowA := main.eventually (Ioi_mem_nhds (show a/2 < a by linarith))
  have lowB := pref.eventually (Ioi_mem_nhds (show b/2 < b by linarith))
  refine ⟨a*b/4,by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,lowA,lowB] with omega pos ma mb
  intro rp rd deficit dr
  have positive : 0 < omega := pos
  have am : a/2*omega^2 ≤ M omega*(1-lossBound omega)-1 :=
    ((lt_div_iff₀ (sq_pos_of_pos positive)).mp ma).le
  have bm : b/2*omega ≤ ‖secondResponsePrefactor n (frequencyParameter omega)‖ :=
    ((lt_div_iff₀ positive).mp mb).le
  have rm : M omega*(1-lossBound omega) ≤ M omega*‖rp‖^2 :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  calc
    _ = (b/2*omega)*(a/2*omega^2) := by ring
    _ ≤ ‖secondResponsePrefactor n (frequencyParameter omega)‖*(M omega*‖rp‖^2-‖rd‖) :=
      mul_le_mul bm (am.trans (by linarith)) (by positivity) (norm_nonneg _)
    _ ≤ _ := printed_second_magnitude_floor n hn _ _ _ (frequency_parameter_real_part omega)

/-- Any parent reflection loss of order strictly higher than omega squared
and a passive daughter give a positive cubic lower bound near zero. -/
theorem second_response_soft_floor (n : ℕ) (hn : 2 ≤ n) (rp rd : ℝ → ℂ)
    (loss : Tendsto (fun omega => (1-‖rp omega‖^2)/omega^2) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (passive : ∀ᶠ omega in 𝓝[>] (0 : ℝ), ‖rd omega‖ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ omega in 𝓝[>] (0 : ℝ),
      c*omega^3 ≤ ‖printedResponse true (frequencyParameter omega) n (rp omega) (rd omega)‖ := by
  obtain ⟨c,cp,h⟩ := second_response_soft_floor_of_loss_bound n hn (fun w => 1-‖rp w‖^2) loss
  refine ⟨c,cp,?_⟩
  filter_upwards [h,passive] with omega bound dp
  exact bound (rp omega) (rd omega) le_rfl dp

/-- A finite coefficient of a power law with exponent over two is
enough for the only scattering limit used in the soft floor. -/
theorem reflection_loss_from_power (rp : ℝ → ℂ) (power : ℕ) (positive : 0 < power)
    (coefficient : ℝ)
    (leading : Tendsto (fun w => (1-‖rp w‖^2)/w^(power+2)) (𝓝[>] (0 : ℝ)) (𝓝 coefficient)) :
    Tendsto (fun w => (1-‖rp w‖^2)/w^2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have freq : Tendsto (fun w : ℝ => w) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have power_limit : Tendsto (fun w : ℝ => w^power) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_pow positive.ne'] using freq.pow power
  have limit := leading.mul power_limit
  simp only [mul_zero] at limit
  apply limit.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have nz : w ≠ 0 := (show 0 < w from hw).ne'
  rw [pow_add]
  field_simp [nz,pow_ne_zero power nz]

#print axioms prefactor_scaled_excess_limit
#print axioms second_prefactor_scaled_limit
#print axioms second_response_soft_floor_of_loss_bound
#print axioms second_response_soft_floor
#print axioms reflection_loss_from_power

end
end SchwarzschildMixtures.Strain
