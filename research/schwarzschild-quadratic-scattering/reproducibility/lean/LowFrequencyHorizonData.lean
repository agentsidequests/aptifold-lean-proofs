import UniformHorizonBranch
import LinearLowFrequencyBarrier

/-! Explicit positive starting data for a unit-horizon wave, uniformly over
a low-frequency interval at each angular degree. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set
open scoped Topology NNReal ENNReal
open SchwarzschildLaurent.Horizon
open SchwarzschildLaurent.Outgoing (radiusLapse)
open SchwarzschildMixtures.Strain

noncomputable section

def horizonSeedDistance (L : ℝ) : ℝ := 1/(16*(100+4*L)^2)

theorem horizon_seed_distance_properties {L : ℝ} (hL : 0 ≤ L) :
    let C := 100+4*L
    let d := horizonSeedDistance L
    1 ≤ C ∧ 0 < d ∧ d ≤ 1 ∧ C*d ≤ 1/4 ∧ 4*C^2*d = 1/4 ∧ d < C⁻¹ := by
  let C : ℝ := 100+4*L
  let d := horizonSeedDistance L
  change 1 ≤ C ∧ 0 < d ∧ d ≤ 1 ∧ C*d ≤ 1/4 ∧ 4*C^2*d = 1/4 ∧ d < C⁻¹
  have c1 : 1 ≤ C := by dsimp [C]; linarith
  have c0 : 0 < C := lt_of_lt_of_le (by norm_num) c1
  have dEq : d = 1/(16*C^2) := rfl
  have d0 : 0 < d := by rw [dEq]; positivity
  have cSq : C ≤ C^2 := by nlinarith [mul_le_mul_of_nonneg_right c1 c0.le]
  have dProduct : C^2*d = 1/16 := by rw [dEq]; field_simp [c0.ne']
  have dSmall := mul_le_mul_of_nonneg_right (c1.trans cSq) d0.le
  have cdSmall := mul_le_mul_of_nonneg_right cSq d0.le
  rw [dProduct,one_mul] at dSmall
  rw [dProduct] at cdSmall
  refine ⟨c1,d0,by linarith,by linarith,by linarith,?_⟩
  rw [← one_div]
  apply (lt_div_iff₀ c0).2
  linarith

private theorem horizon_leading_derivative_re (L omega : ℝ) :
    (((L:ℂ)-3)/(2*(1-4*frequencyParameter omega))).re = (L-3)/(2*(1+16*omega^2)) := by
  let w := 2*(1-4*frequencyParameter omega)
  have wre : w.re = 2 := by
    norm_num [w,frequencyParameter,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
  have wim : w.im = -8*omega := by
    norm_num [w,frequencyParameter,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    ring
  have np : 0 < (1:ℝ)+16*omega^2 := by positivity
  change (((L:ℂ)-3)/w).re = _
  rw [Complex.div_re,Complex.normSq_apply,wre,wim]
  norm_num [Complex.sub_re,Complex.sub_im]
  field_simp [np.ne', show (2:ℝ)*2+(-8*omega)*(-8*omega) ≠ 0 by nlinarith [sq_nonneg omega]]
  ring

theorem positive_horizon_envelope_data {L omega : ℝ} (hL : 6 ≤ L) (wo : 0 < omega)
    (small : omega ≤ 1/(24*(100+4*L))) :
    let d := horizonSeedDistance L
    let H := ingoingEnvelope (frequencyParameter omega) (L:ℂ)
    1-2*(100+4*L)*d ≤ (H (d:ℂ)).re ∧
      d/12 ≤ ((radiusLapse (2+d))*deriv H (d:ℂ)-frequencyParameter omega*H (d:ℂ)).re := by
  let C : ℝ := 100+4*L
  let d := horizonSeedDistance L
  let k := frequencyParameter omega
  let H := ingoingEnvelope k (L:ℂ)
  let a := ((L:ℂ)-3)/(2*(1-4*k))
  change 1-2*C*d ≤ (H (d:ℂ)).re ∧ d/12 ≤ (radiusLapse (2+d)*deriv H (d:ℂ)-k*H (d:ℂ)).re
  obtain ⟨c1,d0,d1,cd,dc,near⟩ := horizon_seed_distance_properties (show 0 ≤ L by linarith)
  change omega ≤ 1/(24*C) at small
  have c0 : 0 < C := lt_of_lt_of_le (by norm_num) c1
  have w24 : omega*(24*C) ≤ 1 := (le_div_iff₀ (by positivity)).1 small
  have w4 : omega ≤ 1/4 := by nlinarith [mul_le_mul_of_nonneg_left c1 wo.le]
  have knorm : ‖k‖ ≤ 1 := by
    have e : ‖k‖ = omega := by simp [k,frequencyParameter,Complex.norm_real,abs_of_pos wo]
    linarith
  have ki : k.re = 0 := by simp [k,frequencyParameter]
  have kim : k.im = omega := by simp [k,frequencyParameter]
  obtain ⟨valueTail,derivTail⟩ := ingoing_seed_tails k L ki knorm (by linarith) d0 cd
  change ‖H (d:ℂ)-1‖ ≤ 2*C*d at valueTail
  change ‖deriv H (d:ℂ)-a‖ ≤ 4*C^2*d at derivTail
  change 4*C^2*d = 1/4 at dc
  rw [dc] at derivTail
  have aRe : 3/4 ≤ a.re := by
    rw [show a.re = _ from horizon_leading_derivative_re L omega]
    apply (le_div_iff₀ (by positivity : 0 < 2*(1+16*omega^2))).2
    nlinarith [mul_nonneg wo.le (sub_nonneg.mpr w4), sq_nonneg (omega-1/4)]
  have derivRe := (Complex.re_le_norm (a-deriv H (d:ℂ))).trans
    (by rwa [norm_sub_rev] : ‖a-deriv H (d:ℂ)‖ ≤ 1/4)
  rw [Complex.sub_re] at derivRe
  have Hder : 1/2 ≤ (deriv H (d:ℂ)).re := by linarith
  have valueRe := (Complex.re_le_norm (1-H (d:ℂ))).trans
    (by rwa [norm_sub_rev] : ‖1-H (d:ℂ)‖ ≤ 2*C*d)
  rw [Complex.sub_re,Complex.one_re] at valueRe
  have valueIm := (abs_le.mp ((Complex.abs_im_le_norm (H (d:ℂ)-1)).trans valueTail)).1
  rw [Complex.sub_im,Complex.one_im,sub_zero] at valueIm
  have F : radiusLapse (2+d) = ((d/(2+d):ℝ):ℂ) := by
    unfold radiusLapse
    push_cast
    ring
  have lapseLower : d/3 ≤ d/(2+d) :=
    div_le_div_of_nonneg_left d0.le (by positivity) (by linarith)
  have positiveF : 0 ≤ d/(2+d) := by positivity
  have first := mul_le_mul lapseLower Hder (by norm_num) positiveF
  have second := mul_le_mul_of_nonneg_left valueIm wo.le
  have wBound : -(d/12) ≤ omega*(-(2*C*d)) := by
    have scaled := mul_le_mul_of_nonneg_right w24 d0.le
    linarith
  refine ⟨by linarith,?_⟩
  rw [F,Complex.sub_re,Complex.mul_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,ki,kim]
  simp only [zero_mul,sub_zero,zero_sub,sub_neg_eq_add]
  linarith

private theorem angular_lower (n : ℕ) (hn : 2 ≤ n) : 6 ≤ (n:ℝ)*(n+1) := by
  have h : (2:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by positivity : 0 ≤ (n:ℝ)+3)]

theorem positive_horizon_wave_data (n : ℕ) (hn : 2 ≤ n) {omega : ℝ} (wo : 0 < omega)
    (small : omega ≤ 1/(24*(100+4*((n:ℝ)*(n+1)))))
    (u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1) :
    let L := (n:ℝ)*(n+1)
    let d := horizonSeedDistance L
    let r := 2+d
    ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
      1-2*(100+4*L)*d ≤ (rotation*u.value r).re ∧ d/12 ≤ (rotation*u.jet r).re := by
  let L : ℝ := (n:ℝ)*(n+1)
  let C : ℝ := 100+4*L
  let d := horizonSeedDistance L
  let r : ℝ := 2+d
  let k := frequencyParameter omega
  let H := normalizedEnvelope k (L:ℂ)
  have l0 : 0 ≤ L := by positivity
  have l6 : 6 ≤ L := angular_lower n hn
  obtain ⟨c1,d0,_,_,_,dR⟩ := horizon_seed_distance_properties l0
  have c0 : 0 < C := lt_of_lt_of_le (by norm_num) c1
  have r2 : 2 < r := by dsimp only [r]; linarith
  have kImag : k.re = 0 := by simp [k,frequencyParameter]
  have kBound : ‖k‖ ≤ 1 := by
    have w : omega*(24*C) ≤ 1 := (le_div_iff₀ (by positivity)).1 small
    have e : ‖k‖ = omega := by simp [k,frequencyParameter,Complex.norm_real,abs_of_pos wo]
    nlinarith [mul_le_mul_of_nonneg_left c1 wo.le]
  let R : ℝ≥0 := ⟨C⁻¹,inv_nonneg.mpr c0.le⟩
  have rp : 0 < R := inv_pos.mpr c0
  have bound : horizonGrowth k (L:ℂ)*(R:ℝ) ≤ 1 := by
    change horizonGrowth k (L:ℂ)*C⁻¹ ≤ 1
    rw [← mul_inv_cancel₀ c0.ne']
    exact mul_le_mul_of_nonneg_right (horizon_growth_uniform k L kBound l0) (inv_nonneg.mpr c0.le)
  have inside : r-2 < (R:ℝ) := by
    change r-2 < C⁻¹
    simpa [r] using dR
  have Lcast : (L:ℂ) = angularEigenvalue n := by simp [L,angularEigenvalue]
  have eq := ingoing_wave_matches_collar k (L:ℂ) kImag rp bound u.value u.jet
    (by rw [Lcast]; exact u.equation) (by rw [Lcast]; exact u.horizon) r2 inside
  have dv : u.value r = ingoingCarrier k (r:ℂ)*H (r:ℂ) := congrArg Prod.fst eq
  have dz : u.jet r = tortoiseDifferential (ingoingWave k H) (r:ℂ) := congrArg Prod.snd eq
  have zeroFree : (r:ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  have close : (r:ℂ)-2 ∈ Metric.eball 0 (R:ℝ≥0∞) := by
    rw [Metric.eball_coe,Metric.mem_ball,dist_eq_norm,sub_zero,← Complex.ofReal_ofNat,
      ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr r2)]
    exact inside
  have analytic := (ingoing_power_series_on_ball k (L:ℂ) kImag rp bound).analyticOnNhd _ close
  have analyticH : AnalyticAt ℂ H (r:ℂ) :=
    analytic.comp (f := fun z : ℂ => z-2) (by fun_prop)
  rw [ingoing_wave_first_derivative k (exterior_log_argument r r2) zeroFree analyticH.differentiableAt] at dz
  let carrier := ingoingCarrier k (r:ℂ)
  have unit : ‖carrier‖ = 1 := by
    simp [carrier,ingoingCarrier,tortoise_real_exterior r r2,Complex.norm_exp,Complex.mul_re,kImag]
  have carrier0 : carrier ≠ 0 := norm_ne_zero_iff.mp (by rw [unit]; norm_num)
  have shift : (r:ℂ)-2 = (d:ℂ) := by simp [r]
  have valueEq : carrier⁻¹*u.value r = ingoingEnvelope k (L:ℂ) (d:ℂ) := by
    rw [dv]
    change carrier⁻¹*(carrier*H (r:ℂ)) = _
    rw [← mul_assoc,inv_mul_cancel₀ carrier0,one_mul]
    simp only [H,normalizedEnvelope,shift]
  have jetEq : carrier⁻¹*u.jet r =
      radiusLapse r*deriv (ingoingEnvelope k (L:ℂ)) (d:ℂ)-k*ingoingEnvelope k (L:ℂ) (d:ℂ) := by
    rw [dz]
    change carrier⁻¹*(carrier*(radiusLapse r*deriv H (r:ℂ)-k*H (r:ℂ))) = _
    rw [← mul_assoc,inv_mul_cancel₀ carrier0,one_mul]
    have slope : deriv H (r:ℂ) = deriv (ingoingEnvelope k (L:ℂ)) (d:ℂ) := by
      change deriv (fun z : ℂ => ingoingEnvelope k (L:ℂ) (z-2)) (r:ℂ) = _
      rw [deriv_comp_sub_const,shift]
    rw [slope]
    simp only [H,normalizedEnvelope,shift]
  obtain ⟨val,jet⟩ := positive_horizon_envelope_data l6 wo small
  refine ⟨carrier⁻¹,by rw [norm_inv,unit,inv_one],?_,?_⟩
  · change 1-2*C*d ≤ (carrier⁻¹*u.value r).re
    rwa [valueEq]
  · change d/12 ≤ (carrier⁻¹*u.jet r).re
    rwa [jetEq]

private theorem inner_barrier_nonnegative (n : ℕ) (hn : 2 ≤ n) {omega d r : ℝ}
    (d0 : 0 < d) (d1 : d ≤ 1) (wbound : omega^2 ≤ d/36) (hr : r ∈ Icc (2+d) 4) :
    0 ≤ realBarrier n omega r := by
  have r2 : (2:ℝ) < r := by linarith [hr.1]
  have r0 : 0 < r := by linarith
  have r4 : r ≤ 4 := hr.2
  have f : d/3 ≤ realLapse r := by
    unfold realLapse
    calc
      _ ≤ d/(2+d) := div_le_div_of_nonneg_left d0.le (by positivity) (by linarith)
      _ ≤ _ := (div_le_div_iff₀ (by positivity) r0).2 (by nlinarith [hr.1])
  have b : 6/r ≤ (3:ℝ) := (div_le_iff₀ r0).2 (by linarith)
  have u : (3:ℝ)/16 ≤ ((n:ℝ)*(n+1)-6/r)/r^2 := by
    have rSq : r^2 ≤ 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr r4) (by positivity : 0 ≤ 4+r)]
    calc
      _ ≤ (3:ℝ)/r^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) rSq
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [angular_lower n hn]) (sq_nonneg r)
  have potential := mul_le_mul f u (by norm_num) (real_lapse_positive r2).le
  unfold realBarrier
  rw [sub_div,div_div,mul_comm r (r^2),← pow_succ] at potential
  linarith

theorem positive_four_mass_seeds (n : ℕ) (hn : 2 ≤ n) {omega : ℝ} (wo : 0 < omega)
    (small : omega ≤ 1/(24*(100+4*((n:ℝ)*(n+1)))))
    (u : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1) :
    let c := horizonSeedDistance ((n:ℝ)*(n+1))/100
    ∃ rotation : ℂ, ‖rotation‖ = 1 ∧ c*4^2 < (rotation*u.value 4).re ∧ 4*c < (rotation*u.jet 4).re := by
  let L : ℝ := (n:ℝ)*(n+1)
  let C : ℝ := 100+4*L
  let d := horizonSeedDistance L
  let r0 : ℝ := 2+d
  obtain ⟨c1,d0,d1,cd,_,_⟩ := horizon_seed_distance_properties (show 0 ≤ L by positivity)
  have c0 : 0 < C := lt_of_lt_of_le (by norm_num) c1
  have endLt : r0 ≤ 4 := by dsimp only [r0]; linarith
  have wo2 : omega^2 ≤ d/36 := by
    calc
      _ ≤ (1/(24*C))^2 := pow_le_pow_left₀ wo.le small _
      _ = _ := by change _ = (1/(16*C^2))/36; field_simp [c0.ne']; ring
  obtain ⟨rot,normRot,hv,hj⟩ := positive_horizon_wave_data n hn wo small u
  let U := u.scale rot
  let y := fun r : ℝ => (U.value r).re
  let z := fun r : ℝ => (U.jet r).re
  let A := fun r => (realLapse r)⁻¹
  let B := fun r => realBarrier n omega r/realLapse r
  have y0 : 0 < y r0 := by
    change 1-2*C*d ≤ y r0 at hv
    linarith
  have z0 : 0 < z r0 := (div_pos d0 (by norm_num : (0:ℝ)<12)).trans_le hj
  have law (r : ℝ) (hr : r ∈ Icc r0 4) :
      HasDerivAt y (A r*z r) r ∧ HasDerivAt z (B r*y r) r :=
    real_exterior_derivatives n omega U.equation (by dsimp only [r0] at hr; linarith [hr.1])
  have nn (r : ℝ) (hr : r ∈ Icc r0 4) : 0 ≤ A r ∧ 0 ≤ B r ∧ 0 ≤ (0:ℝ) := by
    have f := real_lapse_positive (r := r) (by dsimp only [r0] at hr; linarith [hr.1])
    exact ⟨inv_nonneg.mpr f.le,div_nonneg (inner_barrier_nonnegative n hn d0 d1 wo2 hr) f.le,le_rfl⟩
  have pos := forward_positive_pair r0 4 y z A B 0 (fun r hr => (law r hr).1)
    (fun r hr => by simpa only [Pi.zero_apply,add_zero] using (law r hr).2) nn y0 z0
  have monoY := monotone_from_nonnegative_derivative (fun r hr => (law r hr).1)
    (fun r hr => mul_nonneg (nn r hr).1 (pos r hr).2.le)
  have monoZ := monotone_from_nonnegative_derivative (fun r hr => (law r hr).2)
    (fun r hr => mul_nonneg (nn r hr).2.1 (pos r hr).1.le)
  have y4 := monoY ⟨le_rfl,endLt⟩ ⟨endLt,le_rfl⟩ endLt
  have z4 := monoZ ⟨le_rfl,endLt⟩ ⟨endLt,le_rfl⟩ endLt
  change 1-2*C*d ≤ y r0 at hv
  change d/12 ≤ z r0 at hj
  refine ⟨rot,normRot,?_,?_⟩
  · change (d/100)*4^2 < y 4
    linarith
  · change 4*(d/100) < z 4
    linarith

#print axioms horizon_seed_distance_properties
#print axioms positive_horizon_envelope_data
#print axioms positive_horizon_wave_data
#print axioms positive_four_mass_seeds

end
end SchwarzschildLaurent.LinearWave
