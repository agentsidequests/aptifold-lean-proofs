import LinearRetardedUniqueness

/-! A posteriori outgoing-amplitude estimates for the fixed-frequency
Regge–Wheeler equation. Keep both boundary defects and the forcing
residual in the same complex current identity. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set MeasureTheory SchwarzschildLaurent.Outgoing SchwarzschildMixtures
open scoped Topology Interval

noncomputable section

/-- Signed identity for the error field. The outgoing horizon coefficient
is measured in the direction away from the hole, with unit horizon
normalization for the homogeneous test wave. -/
theorem radiation_residual_limit (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L 1) {E e de : ℝ → ℂ} {hin hout ain aout : ℂ}
    (errorEq : RadialEquation radiusLapse (rwPotential w L) E e de)
    (horizon : RadialModeLimits (𝓝[>] (2 : ℝ)) w e de hin hout)
    (infinity : RadialModeLimits atTop w e de ain aout)
    (finite : ∀ a b : ℝ, 2 < a → 2 < b →
      IntervalIntegrable (fun r => u.value r*E r/radiusLapse r) volume a b) :
    Tendsto (fun ab : ℝ × ℝ => ∫ r in ab.1..ab.2, u.value r*E r/radiusLapse r)
      ((𝓝[>] (2 : ℝ)) ×ˢ atTop) (𝓝 (2*w*(u.incoming*aout-u.outgoing*ain-hout))) := by
  have normalized := SchwarzschildMixtures.Strain.normalized_horizon_modes w L 1 hw wi _ _
    u.horizon u.equation.value
  have horizonCurrent : Tendsto (radialCurrent u.value u.jet e de) (𝓝[>] (2 : ℝ)) (𝓝 (2*w*hout)) := by
    change Tendsto (fun r => current (u.value r) (u.jet r) (e r) (de r)) (𝓝[>] (2 : ℝ)) (𝓝 (2*w*hout))
    simpa only [one_mul,zero_mul,sub_zero] using
      current_of_mode_limits _ w hw _ _ u.value u.jet e de
        (fun r => opposite_phases w (realTortoise r)) 1 0 hin hout normalized horizon
  have infinityCurrent := current_of_mode_limits atTop w hw _ _ u.value u.jet e de
    (fun r => opposite_phases w (realTortoise r)) u.incoming u.outgoing ain aout u.infinity infinity
  have limit := green_integral_between_endpoint_limits radiusLapse (rwPotential w L) E
    u.value u.jet e de (2*w*hout) (2*w*(u.incoming*aout-u.outgoing*ain))
    u.equation errorEq finite horizonCurrent infinityCurrent
  have distribute : 2*w*(u.incoming*aout-u.outgoing*ain)-2*w*hout =
      2*w*(u.incoming*aout-u.outgoing*ain-hout) := by ring
  rwa [distribute] at limit

/-- A uniform bound on the absolute weighted residual over finite
exterior intervals suffices for the outgoing coefficient estimate. -/
theorem radiation_error_bound (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L 1) (uin : u.incoming ≠ 0) {E e de : ℝ → ℂ}
    {hin hout ain aout : ℂ} {B : ℝ}
    (errorEq : RadialEquation radiusLapse (rwPotential w L) E e de)
    (horizon : RadialModeLimits (𝓝[>] (2 : ℝ)) w e de hin hout)
    (infinity : RadialModeLimits atTop w e de ain aout)
    (finite : ∀ a b : ℝ, 2 < a → 2 < b →
      IntervalIntegrable (fun r => u.value r*E r/radiusLapse r) volume a b)
    (integralBound : ∀ a b : ℝ, 2 < a → a ≤ b →
      (∫ r in a..b, ‖u.value r*E r/radiusLapse r‖) ≤ B) :
    ‖aout‖ ≤ ‖u.outgoing/u.incoming‖*‖ain‖+‖hout‖/‖u.incoming‖+B/(2*‖w‖*‖u.incoming‖) := by
  let J := 2*w*(u.incoming*aout-u.outgoing*ain-hout)
  have limit := radiation_residual_limit w L hw wi u errorEq horizon infinity finite
  have below : ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), r < 3 := by
    have near : ∀ᶠ r : ℝ in 𝓝 (2 : ℝ), r < 3 := Iio_mem_nhds (by norm_num)
    exact near.filter_mono nhdsWithin_le_nhds
  have bounded : ∀ᶠ ab : ℝ × ℝ in (𝓝[>] (2 : ℝ)) ×ˢ atTop,
      ‖∫ r in ab.1..ab.2, u.value r*E r/radiusLapse r‖ ≤ B := by
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : ∀ᶠ a in 𝓝[>] (2 : ℝ), a ∈ Ioi 2),
      tendsto_fst.eventually below,tendsto_snd.eventually (eventually_ge_atTop (3 : ℝ))]
      with ab ha hleft hright
    have order := hleft.le.trans hright
    exact (intervalIntegral.norm_integral_le_integral_norm order).trans (integralBound _ _ ha order)
  have Jbound : ‖J‖ ≤ B := le_of_tendsto limit.norm bounded
  let R := (u.outgoing/u.incoming)*ain
  let H := hout/u.incoming
  let F := J/(2*w*u.incoming)
  have decompose : aout = R+H+F := by
    dsimp only [R,H,F,J]
    field_simp [hw,uin]
    ring
  have normTwo : ‖(2:ℂ)‖ = 2 := by norm_num
  have forcing : ‖F‖ ≤ B/(2*‖w‖*‖u.incoming‖) := by
    simp only [F,norm_div,norm_mul,normTwo]
    exact div_le_div_of_nonneg_right Jbound (by positivity)
  calc
    ‖aout‖ = ‖R+H+F‖ := congrArg norm decompose
    _ ≤ ‖R‖+‖H‖+‖F‖ := (norm_add_le (R+H) F).trans (add_le_add (norm_add_le R H) le_rfl)
    _ ≤ _ := by
      simp only [R,H,norm_mul,norm_div]
      exact add_le_add le_rfl forcing

theorem ingoing_amplitude_gains (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) :
    1 ≤ ‖u.incoming‖ ∧ ‖u.outgoing/u.incoming‖ < 1 := by
  have flux := ingoing_scattering_flux w hw wi n 1 u
  simp only [← Complex.sq_norm,norm_one,one_pow] at flux
  have inc := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1) (norm_nonneg u.incoming)).mp
    (by nlinarith [sq_nonneg ‖u.outgoing‖])
  have ref := (sq_lt_sq₀ (norm_nonneg u.outgoing) (norm_nonneg u.incoming)).mp (by linarith)
  refine ⟨inc,?_⟩
  rw [norm_div, div_lt_one (by linarith : 0 < ‖u.incoming‖)]
  exact ref

theorem unit_horizon_reflected_fraction (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) :
    ‖u.outgoing/u.incoming‖^2 = 1-1/‖u.incoming‖^2 := by
  have flux := ingoing_scattering_flux w hw wi n 1 u
  simp only [← Complex.sq_norm,norm_one,one_pow] at flux
  have pos := (ingoing_amplitude_gains w n hw wi u).1
  have nz : ‖u.incoming‖ ≠ 0 := ne_of_gt (by linarith)
  rw [norm_div,div_pow]
  field_simp [nz]
  linarith

/-- The finite modal norm bounds the incident amplitude at infinity
through the remaining inverse-square tail. -/
theorem incident_lower_from_modal_norm (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) {R : ℝ} (hR : 2 < R) :
    ‖modalCoefficients w u.value u.jet R‖*Real.exp (-((‖angularEigenvalue n‖+3)/‖w‖)/R) ≤
      ‖u.incoming‖ := by
  let L := angularEigenvalue n
  let C := (‖L‖+3)/‖w‖
  let A := modalCoefficients w u.value u.jet
  have limit : Tendsto A atTop (𝓝 (u.incoming,u.outgoing)) :=
    u.infinity.incoming.prodMk_nhds u.infinity.outgoing
  have bound := inverse_square_backward_bound A (fun r => modalDerivative w L r (A r)) C
    (by dsimp only [C]; positivity)
    (fun r hr => modal_coefficients_derivative w L hw u.value u.jet r hr u.equation)
    (fun r hr => modal_derivative_bound w L hw wi r hr (A r)) limit hR
  obtain ⟨pos,reflect⟩ := ingoing_amplitude_gains w n hw wi u
  rw [norm_div,div_lt_one (by linarith : 0 < ‖u.incoming‖)] at reflect
  have limiting_norm : ‖(u.incoming,u.outgoing)‖ = ‖u.incoming‖ := max_eq_left reflect.le
  rw [limiting_norm] at bound
  change _ * Real.exp (-C/R) ≤ _
  calc
    _ ≤ (‖u.incoming‖*Real.exp (C/R))*Real.exp (-C/R) :=
      mul_le_mul_of_nonneg_right bound (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,← Real.exp_add,neg_div,add_neg_cancel,Real.exp_zero,mul_one]

theorem incident_lower_from_radius (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) {R : ℝ} (hR : 2 < R) :
    ‖(u.value R-u.jet R/w)/2‖*Real.exp (-((‖angularEigenvalue n‖+3)/‖w‖)/R) ≤ ‖u.incoming‖ := by
  let A := modalCoefficients w u.value u.jet
  have coefficient : ‖(A R).1‖ = ‖(u.value R-u.jet R/w)/2‖ := by
    change ‖(u.value R-u.jet R/w)*outgoingCarrier w R/2‖ = _
    simp only [norm_div,norm_mul,outgoingCarrier,phase_norm w wi,mul_one]
  rw [← coefficient]
  exact (mul_le_mul_of_nonneg_right (norm_fst_le (A R)) (Real.exp_pos _).le).trans
    (incident_lower_from_modal_norm w n hw wi u hR)

/-- A lower bound on wave size alone controls incidence, even when
the finite-radius phase and jet are unavailable. -/
theorem incident_lower_from_value (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) {R : ℝ} (hR : 2 < R) :
    (‖u.value R‖/2)*Real.exp (-((‖angularEigenvalue n‖+3)/‖w‖)/R) ≤ ‖u.incoming‖ := by
  let A := modalCoefficients w u.value u.jet R
  let m := incomingCarrier w R
  let p := outgoingCarrier w R
  have value : wave A.1 A.2 m p = u.value R :=
    (reconstruct_modes w m p _ _ hw (opposite_phases w (realTortoise R))).1
  have m1 : ‖m‖ = 1 := phase_norm (-w) (by simp [wi]) _
  have p1 : ‖p‖ = 1 := phase_norm w wi _
  have half : ‖u.value R‖/2 ≤ ‖A‖ := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).2
    rw [← value,wave]
    calc
      _ ≤ ‖A.1*m‖+‖A.2*p‖ := norm_add_le _ _
      _ = ‖A.1‖+‖A.2‖ := by simp only [norm_mul,m1,p1,mul_one]
      _ ≤ ‖A‖+‖A‖ := add_le_add (norm_fst_le A) (norm_snd_le A)
      _ = _ := by ring
  calc
    _ ≤ ‖A‖*Real.exp (-((‖angularEigenvalue n‖+3)/‖w‖)/R) :=
      mul_le_mul_of_nonneg_right half (Real.exp_pos _).le
    _ ≤ _ := incident_lower_from_modal_norm w n hw wi u hR

/-- The two boundary leakage gains have squared magnitudes summing to
one. This contracts the joint Euclidean error in the radiation data. -/
theorem boundary_leakage_bound (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) (ain hout : ℂ) :
    ‖u.outgoing/u.incoming‖*‖ain‖+‖hout‖/‖u.incoming‖ ≤ Real.sqrt (‖ain‖^2+‖hout‖^2) := by
  let r := ‖u.outgoing/u.incoming‖
  let t := 1/‖u.incoming‖
  let a := ‖ain‖
  let h := ‖hout‖
  have flux := ingoing_scattering_flux w hw wi n 1 u
  simp only [← Complex.sq_norm,norm_one,one_pow] at flux
  have pos := (ingoing_amplitude_gains w n hw wi u).1
  have n0 : ‖u.incoming‖ ≠ 0 := ne_of_gt (by linarith)
  have unit : r^2+t^2 = 1 := by
    dsimp only [r,t]
    rw [norm_div,div_pow,div_pow,one_pow,← add_div,← flux,div_self (pow_ne_zero 2 n0)]
  have identity : (r*a+t*h)^2+(r*h-t*a)^2 = a^2+h^2 := by
    calc
      _ = (r^2+t^2)*(a^2+h^2) := by ring
      _ = _ := by rw [unit,one_mul]
  have square : (r*a+t*h)^2 ≤ a^2+h^2 := by
    linarith [sq_nonneg (r*h-t*a)]
  have bound : r*a+t*h ≤ Real.sqrt (a^2+h^2) := by
    apply (sq_le_sq₀ (by dsimp only [r,t,a,h]; positivity) (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt (by positivity)]
  simpa only [r,t,a,h,one_div,div_eq_mul_inv,one_mul,mul_comm (‖u.incoming‖⁻¹)] using bound

/-- Compare a candidate to the exact retarded solution for its intended
source. The residual is the candidate source minus the intended source. -/
theorem retarded_amplitude_error (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) {S T p dp v dv : ℝ → ℂ}
    {q hin hout ain aout : ℂ} {B : ℝ}
    (reference : RadialEquation radiusLapse (rwPotential w (angularEigenvalue n)) S p dp)
    (retarded : RetardedBoundary w p dp q)
    (candidate : RadialEquation radiusLapse (rwPotential w (angularEigenvalue n)) T v dv)
    (horizon : RadialModeLimits (𝓝[>] (2 : ℝ)) w v dv hin hout)
    (infinity : RadialModeLimits atTop w v dv ain aout)
    (finite : ∀ a b : ℝ, 2 < a → 2 < b →
      IntervalIntegrable (fun r => u.value r*(T r-S r)/radiusLapse r) volume a b)
    (integralBound : ∀ a b : ℝ, 2 < a → a ≤ b →
      (∫ r in a..b, ‖u.value r*(T r-S r)/radiusLapse r‖) ≤ B) :
    ‖aout-q‖ ≤ ‖u.outgoing/u.incoming‖*‖ain‖+‖hout‖/‖u.incoming‖+B/(2*‖w‖*‖u.incoming‖) := by
  obtain ⟨t,atHorizon⟩ := retarded.horizon
  have uin : u.incoming ≠ 0 := nonzero_incident_amplitude (ingoing_scattering_flux w hw wi n 1 u) (by norm_num)
  have eq := radial_equation_sub_scaled 1 candidate reference
  have h := radial_mode_limits_sub_scaled 1 horizon atHorizon
  have i := radial_mode_limits_sub_scaled 1 infinity retarded.infinity
  simp only [one_mul,sub_zero] at eq h i
  exact radiation_error_bound w (angularEigenvalue n) hw wi u uin eq h i finite integralBound

#print axioms radiation_residual_limit
#print axioms radiation_error_bound
#print axioms ingoing_amplitude_gains
#print axioms unit_horizon_reflected_fraction
#print axioms incident_lower_from_modal_norm
#print axioms incident_lower_from_radius
#print axioms incident_lower_from_value
#print axioms boundary_leakage_bound
#print axioms retarded_amplitude_error

end
end SchwarzschildLaurent.LinearWave
