import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The bilinear Green current and the finite-to-infinite integration
step in areal radius. The jets supplied to the current are derivatives
in tortoise radius. -/
namespace SchwarzschildLaurent.Outgoing

open Filter Set MeasureTheory
open scoped Topology Interval

noncomputable section

def current (u du p dp : ℂ) : ℂ := u*dp-p*du

def radialCurrent (u du p dp : ℝ → ℂ) (r : ℝ) : ℂ :=
  current (u r) (du r) (p r) (dp r)

/-- Derivatives in areal radius for a value and its tortoise jet.
The potential here includes the constant frequency-squared term. -/
structure RadialEquation (f V S u du : ℝ → ℂ) : Prop where
  value : ∀ r : ℝ, 2 < r → HasDerivAt u (du r/f r) r
  jet : ∀ r : ℝ, 2 < r → HasDerivAt du ((V r*u r+S r)/f r) r

theorem green_current_derivative (f V S u du p dp : ℝ → ℂ)
    (homogeneous : RadialEquation f V 0 u du) (particular : RadialEquation f V S p dp)
    {r : ℝ} (hr : 2 < r) :
    HasDerivAt (radialCurrent u du p dp) (u r*S r/f r) r := by
  have d := ((homogeneous.value r hr).mul (particular.jet r hr)).sub
    ((particular.value r hr).mul (homogeneous.jet r hr))
  apply d.congr_deriv
  simp only [Pi.zero_apply, add_zero, div_eq_mul_inv]
  ring

theorem green_integral_on_interval (f V S u du p dp : ℝ → ℂ)
    (homogeneous : RadialEquation f V 0 u du) (particular : RadialEquation f V S p dp)
    {a b : ℝ} (ha : 2 < a) (hb : 2 < b)
    (integrable : IntervalIntegrable (fun r => u r*S r/f r) volume a b) :
    (∫ r in a..b, u r*S r/f r) = radialCurrent u du p dp b-radialCurrent u du p dp a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ integrable
  intro r hr
  exact green_current_derivative f V S u du p dp homogeneous particular
    ((lt_min ha hb).trans_le hr.1)

/-- Both radial cutoffs tend to their endpoints independently. -/
theorem green_integral_between_endpoint_limits (f V S u du p dp : ℝ → ℂ) (whorizon winfty : ℂ)
    (homogeneous : RadialEquation f V 0 u du) (particular : RadialEquation f V S p dp)
    (integrable : ∀ a b : ℝ, 2 < a → 2 < b →
      IntervalIntegrable (fun r => u r*S r/f r) volume a b)
    (at_horizon : Tendsto (radialCurrent u du p dp) (𝓝[>] (2 : ℝ)) (𝓝 whorizon))
    (at_infinity : Tendsto (radialCurrent u du p dp) atTop (𝓝 winfty)) :
    Tendsto (fun ab : ℝ × ℝ => ∫ r in ab.1..ab.2, u r*S r/f r)
      ((𝓝[>] (2 : ℝ)) ×ˢ atTop) (𝓝 (winfty-whorizon)) := by
  have hp := at_horizon.comp
    (tendsto_fst : Tendsto Prod.fst ((𝓝[>] (2 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝[>] (2 : ℝ)))
  have hi := at_infinity.comp
    (tendsto_snd : Tendsto Prod.snd ((𝓝[>] (2 : ℝ)) ×ˢ (atTop : Filter ℝ)) atTop)
  have limit := hi.sub hp
  apply limit.congr'
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : ∀ᶠ a in 𝓝[>] (2 : ℝ), a ∈ Ioi 2),
    tendsto_snd.eventually (eventually_gt_atTop (2 : ℝ))] with ab ha hb
  exact (green_integral_on_interval f V S u du p dp homogeneous particular
    ha hb (integrable _ _ ha hb)).symm

theorem green_integral_from_endpoint_limits (f V S u du p dp : ℝ → ℂ) (winfty : ℂ)
    (homogeneous : RadialEquation f V 0 u du) (particular : RadialEquation f V S p dp)
    (integrable : ∀ a b : ℝ, 2 < a → 2 < b →
      IntervalIntegrable (fun r => u r*S r/f r) volume a b)
    (at_horizon : Tendsto (radialCurrent u du p dp) (𝓝[>] (2 : ℝ)) (𝓝 0))
    (at_infinity : Tendsto (radialCurrent u du p dp) atTop (𝓝 winfty)) :
    Tendsto (fun ab : ℝ × ℝ => ∫ r in ab.1..ab.2, u r*S r/f r)
      ((𝓝[>] (2 : ℝ)) ×ˢ atTop) (𝓝 winfty) := by
  simpa only [sub_zero] using green_integral_between_endpoint_limits f V S u du p dp 0 winfty
    homogeneous particular integrable at_horizon at_infinity

/-- Products of the two oscillatory carriers are exactly one. This
fixes the sign of the reflected contribution and the factor \(4k\). -/
theorem signed_current (w : ℂ) (phaseMinus phasePlus : ℂ)
    (phases : phaseMinus*phasePlus = 1)
    (uin uout pin pout : ℂ) :
    current (uin*phaseMinus+uout*phasePlus) (w*(uout*phasePlus-uin*phaseMinus))
      (pin*phaseMinus+pout*phasePlus) (w*(pout*phasePlus-pin*phaseMinus)) =
      2*w*(uin*pout-uout*pin) := by
  unfold current
  calc
    _ = phaseMinus*phasePlus*(2*w*(uin*pout-uout*pin)) := by ring
    _ = _ := by rw [phases, one_mul]

theorem normalized_green_response (k uin uout pin pout : ℂ)
    (hk : k ≠ 0) (hi : uin ≠ 0) :
    (2*(2*k)*(uin*pout-uout*pin))/(4*k*uin) =
      pout-pin*(uout/uin) := by
  field_simp [hk,hi]
  ring

/-- The same complex coefficient follows by homogeneous subtraction,
which imposes zero incoming amplitude on the completed field. -/
theorem homogeneous_subtraction (uin uout pin pout : ℂ) (hi : uin ≠ 0) :
    pin-(pin/uin)*uin = 0 ∧ pout-(pin/uin)*uout = pout-pin*(uout/uin) := by
  constructor
  · rw [div_mul_cancel₀ _ hi, sub_self]
  · ring

#print axioms green_current_derivative
#print axioms green_integral_on_interval
#print axioms green_integral_between_endpoint_limits
#print axioms green_integral_from_endpoint_limits
#print axioms signed_current
#print axioms normalized_green_response
#print axioms homogeneous_subtraction

end
end SchwarzschildLaurent.Outgoing
