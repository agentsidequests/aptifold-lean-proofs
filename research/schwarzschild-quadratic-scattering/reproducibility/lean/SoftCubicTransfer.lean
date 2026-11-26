import SoftExpansionAlgebra
import SoftCubicSign

/-! The phase-corrected cubic response and the slope of its magnitude.
The asymptotic input is stated on the two linear reflection factors. -/
namespace SchwarzschildMixtures.Strain

open Filter Set
open SchwarzschildLaurent.Outgoing (printedScale)
open scoped Topology

noncomputable section

def secondThresholdFactor (g G a b : ℝ) : ℝ :=
  1/g^2+2/(g*G)+1/G^2-(a-b)/G

def phaseRemovedSecondResponse (n : ℕ) (p d : ℝ → ℂ) (w : ℝ) : ℂ :=
  let g := parentRate n
  let G := daughterRate n
  ((printedScale n/(4*G):ℝ):ℂ)*frequencyParameter w*
    (evenEnvelopeWeight (g:ℂ) (G:ℂ) w*p w-oddEnvelopeWeight (G:ℂ) w*d w)

theorem phase_removed_second_response_eq (n : ℕ) (w : ℝ) (rp rd F : ℂ) :
    phaseRemovedSecondResponse n (fun _ => rp^2/F) (fun _ => -rd/F) w =
      printedResponse true (frequencyParameter w) n rp rd/F := by
  have daughter : (daughterRate n:ℂ) = daughterGamma (n:ℂ) := by
    simp [daughterRate,daughterGamma,parent_rate_cast,Nat.cast_mul]
  unfold phaseRemovedSecondResponse printedResponse evenEnvelopeWeight oddEnvelopeWeight
  simp only [if_true,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,parent_rate_cast,daughter]
  ring

theorem phase_removed_second_cubic (n : ℕ) (hn : 2 ≤ n) (p d : ℝ → ℂ) (a b : ℝ)
    (hp : Tendsto (quadraticQuotient p 1 (a:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (((a^2/2:ℝ):ℂ)+((8*Real.pi*spinTwoAngularCorrection n:ℝ):ℂ)*Complex.I)))
    (hd : Tendsto (quadraticQuotient d 1 (b:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (((b^2/2:ℝ):ℂ)+((16*Real.pi*spinTwoAngularCorrection (2*n):ℝ):ℂ)*Complex.I))) :
    let G := daughterRate n
    let η := printedScale n/(4*G)
    let C := -η*secondThresholdFactor (parentRate n) G a b
    ∃ B : ℂ,
      Tendsto (fun w => (phaseRemovedSecondResponse n p d w/(w:ℂ)^2-(C:ℂ))/(w:ℂ))
        (𝓝[>] (0:ℝ)) (𝓝 B) ∧
      B.re = -η*8*Real.pi/G*angularPhaseDifference n := by
  let g := parentRate n
  let G := daughterRate n
  let η := printedScale n/(4*G)
  let v := secondThresholdFactor g G a b
  let gp := (g:ℂ)
  let Gp := (G:ℂ)
  let a₀ : ℂ := -1/Gp
  let e₁ : ℂ := 1/gp^2+2/(gp*Gp)
  let o₁ : ℂ := -1/Gp^2
  let e₂ : ℂ := (-2/gp-3/Gp)/gp^2
  let o₂ : ℂ := -1/Gp^3
  let qP : ℂ := ((a^2/2:ℝ):ℂ)+((8*Real.pi*spinTwoAngularCorrection n:ℝ):ℂ)*Complex.I
  let qD : ℂ := ((b^2/2:ℝ):ℂ)+((16*Real.pi*spinTwoAngularCorrection (2*n):ℝ):ℂ)*Complex.I
  let B₂ := (e₂+e₁*(a:ℂ)+a₀*qP)-(o₂+o₁*(b:ℂ)+a₀*qD)
  let H := fun w => evenEnvelopeWeight gp Gp w*p w-oddEnvelopeWeight Gp w*d w
  have gpos := parent_rate_positive n hn
  have Gpos := gpos.trans (daughter_rate_gt_parent n hn)
  have g0 : gp ≠ 0 := Complex.ofReal_ne_zero.mpr gpos.ne'
  have G0 : Gp ≠ 0 := Complex.ofReal_ne_zero.mpr Gpos.ne'
  have e := quadratic_quotient_product (even_envelope_weight_expansion gp Gp g0 G0) hp
  have o := quadratic_quotient_product (odd_envelope_weight_expansion Gp G0) hd
  have value := e.sub o
  simp only [mul_one] at value
  have first : (e₁+a₀*(a:ℂ))-(o₁+a₀*(b:ℂ)) = (v:ℂ) := by
    dsimp only [v,secondThresholdFactor,e₁,o₁,a₀,gp,Gp]
    push_cast
    ring
  have Hlimit : Tendsto (quadraticQuotient H 0 (v:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 B₂) := by
    apply value.congr
    intro w
    unfold quadraticQuotient H
    simp only [sub_zero]
    rw [← first]
    change (_-a₀-(e₁+a₀*(a:ℂ))*frequencyParameter w)/(frequencyParameter w)^2-
      (_-a₀-(o₁+a₀*(b:ℂ))*frequencyParameter w)/(frequencyParameter w)^2 = _
    ring
  have raw := Hlimit.const_mul (-Complex.I*(η:ℂ))
  refine ⟨-Complex.I*(η:ℂ)*B₂,?_,?_⟩
  · apply raw.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    let W := (w:ℂ)
    let k := frequencyParameter w
    have W0 : W ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0 < w from hw).ne'
    have ks : k^2 = -W^2 := by
      dsimp only [k,W,frequencyParameter]
      rw [mul_pow,Complex.I_sq,mul_neg, mul_one]
    have kEq : k = W*Complex.I := rfl
    change -Complex.I*(η:ℂ)*((H w-0-(v:ℂ)*k)/k^2) =
      ((η:ℂ)*k*H w/W^2-((-η*v:ℝ):ℂ))/W
    rw [ks,kEq,sub_zero,Complex.ofReal_mul,Complex.ofReal_neg]
    field_simp [W0]
    ring_nf
    rw [Complex.I_sq]
    ring
  · have ei : e₁.im = 0 := by
      change (1/(g:ℂ)^2+2/((g:ℂ)*(G:ℂ))).im = 0
      norm_cast
    have oi : o₁.im = 0 := by change (-1/(G:ℂ)^2).im = 0; norm_cast
    have eii : e₂.im = 0 := by change ((-2/(g:ℂ)-3/(G:ℂ))/(g:ℂ)^2).im = 0; norm_cast
    have oii : o₂.im = 0 := by change (-1/(G:ℂ)^3).im = 0; norm_cast
    have aRe : a₀.re = -1/G := by change (-1/(G:ℂ)).re = _; norm_cast
    have aIm : a₀.im = 0 := by change (-1/(G:ℂ)).im = 0; norm_cast
    have qPIm : qP.im = 8*Real.pi*spinTwoAngularCorrection n := by
      simp only [qP,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    have qDIm : qD.im = 16*Real.pi*spinTwoAngularCorrection (2*n) := by
      simp only [qD,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    have diff : B₂.im = -8*Real.pi/G*angularPhaseDifference n := by
      dsimp only [B₂]
      simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
        ei,oi,eii,oii,aRe,aIm,qPIm,qDIm,zero_mul,mul_zero,zero_add,add_zero,angularPhaseDifference]
      ring
    change (-Complex.I*(η:ℂ)*B₂).re = _
    simp [Complex.mul_re,Complex.mul_im,diff]
    ring

/-- A negative real leading amplitude makes the normalized magnitude
slope the real component of its complex correction divided by the lead. -/
theorem magnitude_slope_at_negative_real {z : ℝ → ℂ} {C : ℝ} {B : ℂ} (neg : C < 0)
    (derivative : Tendsto (fun w => (z w-(C:ℂ))/(w:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 B)) :
    Tendsto (fun w => (‖z w‖/(-C)-1)/w) (𝓝[>] (0:ℝ)) (𝓝 (B.re/C)) := by
  let q := fun w : ℝ => (z w-(C:ℂ))/(w:ℂ)
  have freq : Tendsto (fun w : ℝ => w) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have freqC : Tendsto (fun w : ℝ => (w:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp freq
  have exactQ (w : ℝ) (wp : 0 < w) : z w = (C:ℂ)+(w:ℂ)*q w := by
    dsimp only [q]
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr wp.ne')]
    ring
  have zT : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 (C:ℂ)) := by
    have t := (freqC.mul derivative).const_add (C:ℂ)
    simp only [zero_mul,add_zero] at t
    apply t.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (exactQ w hw).symm
  have reQ : Tendsto (fun w => (q w).re) (𝓝[>] (0:ℝ)) (𝓝 B.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp derivative
  have sq : Tendsto (fun w => (‖z w‖^2-C^2)/w) (𝓝[>] (0:ℝ)) (𝓝 (2*C*B.re)) := by
    have t := (reQ.const_mul (2*C)).add (freq.mul (derivative.norm.pow 2))
    simp only [zero_mul,add_zero] at t
    apply t.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    have w0 := (show 0 < w from hw).ne'
    change 2*C*(q w).re+w*‖q w‖^2 = _
    rw [exactQ w hw]
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,zero_mul,sub_zero,add_zero]
    field_simp [w0]
    ring
  have zN : Tendsto (fun w => ‖z w‖) (𝓝[>] (0:ℝ)) (𝓝 (-C)) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_neg neg] using zT.norm
  have nonzero : (-C)*(-C-C) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have t := sq.div ((zN.sub_const C).const_mul (-C)) nonzero
  have base : (2*C*B.re)/((-C)*(-C-C)) = B.re/C := by
    field_simp [neg.ne]
    ring
  rw [base] at t
  apply t.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have w0 := (show 0 < w from hw).ne'
  have lower : ‖z w‖-C ≠ 0 := by linarith [norm_nonneg (z w)]
  change ((‖z w‖^2-C^2)/w)/((-C)*(‖z w‖-C)) = _
  field_simp [w0,neg.ne,lower]
  ring

theorem second_magnitude_slope_from_linear_phases (n : ℕ) (hn : 2 ≤ n)
    (rp rd F : ℝ → ℂ) (a b : ℝ) (unit : ∀ w, ‖F w‖ = 1)
    (hp : Tendsto (quadraticQuotient (fun w => (rp w)^2/F w) 1 (a:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (((a^2/2:ℝ):ℂ)+((8*Real.pi*spinTwoAngularCorrection n:ℝ):ℂ)*Complex.I)))
    (hd : Tendsto (quadraticQuotient (fun w => -rd w/F w) 1 (b:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (((b^2/2:ℝ):ℂ)+((16*Real.pi*spinTwoAngularCorrection (2*n):ℝ):ℂ)*Complex.I)))
    (positive : 0 < secondThresholdFactor (parentRate n) (daughterRate n) a b) :
    let G := daughterRate n
    let η := printedScale n/(4*G)
    let v := secondThresholdFactor (parentRate n) G a b
    Tendsto (fun w => (‖printedResponse true (frequencyParameter w) n (rp w) (rd w)‖/(η*v*w^2)-1)/w)
      (𝓝[>] (0:ℝ)) (𝓝 (8*Real.pi/(G*v)*angularPhaseDifference n)) := by
  let p := fun w => (rp w)^2/F w
  let d := fun w => -rd w/F w
  let G := daughterRate n
  let η := printedScale n/(4*G)
  let v := secondThresholdFactor (parentRate n) G a b
  let z := fun w => phaseRemovedSecondResponse n p d w/(w:ℂ)^2
  have gp := parent_rate_positive n hn
  have Gp := gp.trans (daughter_rate_gt_parent n hn)
  have ηp : 0 < η := div_pos (printed_scale_positive n hn) (by positivity)
  obtain ⟨B,Bderiv,Bre⟩ := phase_removed_second_cubic n hn p d a b hp hd
  change B.re = -η*8*Real.pi/G*angularPhaseDifference n at Bre
  have neg : -η*v < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos ηp) positive
  have mag := magnitude_slope_at_negative_real (z := z) neg Bderiv
  have out : B.re/(-η*v) = 8*Real.pi/(G*v)*angularPhaseDifference n := by
    rw [Bre]
    field_simp [ηp.ne',Gp.ne',positive.ne']
  rw [out] at mag
  apply mag.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have wp : 0 < w := hw
  have e := phase_removed_second_response_eq n w (rp w) (rd w) (F w)
  have here : phaseRemovedSecondResponse n p d w =
      printedResponse true (frequencyParameter w) n (rp w) (rd w)/F w := e
  simp only [z,here,norm_div,norm_pow,unit,div_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos wp,neg_mul,neg_neg]
  ring

#print axioms phase_removed_second_response_eq
#print axioms phase_removed_second_cubic
#print axioms magnitude_slope_at_negative_real
#print axioms second_magnitude_slope_from_linear_phases

end
end SchwarzschildMixtures.Strain
