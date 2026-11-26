import RetardedStrainError

/-! A complex amplitude enclosure from a finite Wronskian readout
and a bound on the trial wave's exterior residual. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set MeasureTheory SchwarzschildLaurent.Outgoing SchwarzschildMixtures
open scoped Topology Interval

noncomputable section

def exteriorWaveBound (w L : ℂ) (u du : ℝ → ℂ) (R : ℝ) : ℝ :=
  2*‖modalCoefficients w u du R‖*Real.exp (((‖L‖+3)/‖w‖)/R)

theorem exterior_wave_norm_bound {w L : ℂ} (hw : w ≠ 0) (wi : w.re = 0)
    {u du : ℝ → ℂ} (equation : RadialEquation radiusLapse (rwPotential w L) 0 u du)
    {R r : ℝ} (hR : 2 < R) (hr : R ≤ r) : ‖u r‖ ≤ exteriorWaveBound w L u du R := by
  let A := modalCoefficients w u du
  let C := (‖L‖+3)/‖w‖
  have inside : 2 < r := hR.trans_le hr
  have modalBound := inverse_square_forward_bound A (fun s => modalDerivative w L s (A s)) C
    (fun s hs => modal_coefficients_derivative w L hw u du s hs equation)
    (fun s hs => modal_derivative_bound w L hw wi s hs (A s)) hR hr
  have power : C*(R⁻¹-r⁻¹) ≤ C/R := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr (by linarith))) (by dsimp [C]; positivity)
  have phase : incomingCarrier w r*outgoingCarrier w r = 1 :=
    opposite_phases w (realTortoise r)
  have oneIn : ‖incomingCarrier w r‖ = 1 :=
    phase_norm (-w) (by simp [wi]) (realTortoise r)
  have oneOut : ‖outgoingCarrier w r‖ = 1 := phase_norm w wi (realTortoise r)
  have raw := (reconstruct_modes w (incomingCarrier w r) (outgoingCarrier w r) (u r) (du r)
    hw phase).1
  change wave (A r).1 (A r).2 (incomingCarrier w r) (outgoingCarrier w r) = u r at raw
  calc
    ‖u r‖ = ‖wave (A r).1 (A r).2 (incomingCarrier w r) (outgoingCarrier w r)‖ := by rw [raw]
    _ ≤ ‖(A r).1‖+‖(A r).2‖ := by
      unfold wave
      simpa only [norm_mul,oneIn,oneOut,mul_one] using norm_add_le
        ((A r).1*incomingCarrier w r) ((A r).2*outgoingCarrier w r)
    _ ≤ 2*‖A r‖ := by
      rw [two_mul]
      exact add_le_add (norm_fst_le _) (norm_snd_le _)
    _ ≤ 2*(‖A R‖*Real.exp (C*(R⁻¹-r⁻¹))) := mul_le_mul_of_nonneg_left modalBound (by norm_num)
    _ ≤ exteriorWaveBound w L u du R := by
      change _ ≤ 2*‖A R‖*Real.exp (C/R)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr power) (by positivity)

/-- If the trial wave is normalized to unit outgoing amplitude, the left
side is the error in the incident coefficient. A unit incoming trial
wave instead returns the negative of the reflected coefficient. -/
theorem finite_wronskian_readout_bound {w L : ℂ} (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L 1) {E p dp : ℝ → ℂ}
    (trial : RadialEquation radiusLapse (rwPotential w L) E p dp)
    {pin pout : ℂ} (modes : RadialModeLimits atTop w p dp pin pout)
    {R B : ℝ} (hR : 2 < R)
    (continuous : ContinuousOn (fun r => E r/radiusLapse r) (Ioi 2))
    (tail : ∀ s : ℝ, R ≤ s → (∫ r in R..s, ‖E r/radiusLapse r‖) ≤ B) :
    ‖u.incoming*pout-u.outgoing*pin-radialCurrent u.value u.jet p dp R/(2*w)‖ ≤
      exteriorWaveBound w L u.value u.jet R*B/(2*‖w‖) := by
  let N := exteriorWaveBound w L u.value u.jet R
  let T := u.incoming*pout-u.outgoing*pin
  let J := radialCurrent u.value u.jet p dp
  have N0 : 0 ≤ N := by dsimp [N,exteriorWaveBound]; positivity
  have limit : Tendsto J atTop (𝓝 (2*w*T)) :=
    current_of_mode_limits atTop w hw _ _ u.value u.jet p dp
      (fun r => opposite_phases w (realTortoise r)) u.incoming u.outgoing pin pout u.infinity modes
  have finite (s : ℝ) (hs : R ≤ s) : ‖J s-J R‖ ≤ N*B := by
    have subI : Icc R s ⊆ Ioi 2 := fun _ ht => hR.trans_le ht.1
    have uC : ContinuousOn u.value (Ioi 2) := fun r hr =>
      (u.equation.value r hr).continuousAt.continuousWithinAt
    have fC : ContinuousOn (fun r => u.value r*(E r/radiusLapse r)) (Icc R s) :=
      (uC.mul continuous).mono subI
    have integrable : IntervalIntegrable (fun r => u.value r*E r/radiusLapse r) volume R s := by
      simpa only [mul_div_assoc] using fC.intervalIntegrable_of_Icc hs
    have integral := green_integral_on_interval radiusLapse (rwPotential w L) E
      u.value u.jet p dp u.equation trial hR (hR.trans_le hs) integrable
    have compare := intervalIntegral.integral_mono_on hs integrable.norm
      (((continuous.norm.const_mul N).mono subI).intervalIntegrable_of_Icc hs)
      (fun x hx => by
        rw [mul_div_assoc,norm_mul]
        exact mul_le_mul_of_nonneg_right (exterior_wave_norm_bound hw wi u.equation hR hx.1) (norm_nonneg _))
    rw [intervalIntegral.integral_const_mul] at compare
    change ‖radialCurrent u.value u.jet p dp s-radialCurrent u.value u.jet p dp R‖ ≤ _
    rw [← integral]
    exact (intervalIntegral.norm_integral_le_integral_norm hs).trans
      (compare.trans (mul_le_mul_of_nonneg_left (tail s hs) N0))
  have bound : ‖2*w*T-J R‖ ≤ N*B :=
    le_of_tendsto (limit.sub_const (J R)).norm ((eventually_ge_atTop R).mono finite)
  have divide : T-J R/(2*w) = (2*w*T-J R)/(2*w) := by
    field_simp [hw]
  change ‖T-J R/(2*w)‖ ≤ _
  rw [divide,norm_div,norm_mul,show ‖(2:ℂ)‖ = 2 by norm_num]
  exact div_le_div_of_nonneg_right bound (by positivity)

#print axioms exterior_wave_norm_bound
#print axioms finite_wronskian_readout_bound

end
end SchwarzschildLaurent.LinearWave
