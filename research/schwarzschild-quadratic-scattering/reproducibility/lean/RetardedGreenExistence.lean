import RetardedGreenFunction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Existence from the retarded Green integral for an exterior source
with absolutely integrable homogeneous-wave weights. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set MeasureTheory ComplexConjugate
open SchwarzschildLaurent.Outgoing SchwarzschildMixtures
open scoped Topology Interval

noncomputable section

def exteriorPrimitive (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ x in 2..r, (Ioi (2 : ℝ)).indicator f x

private theorem exteriorPrimitive_deriv {f : ℝ → ℂ}
    (integrable : IntegrableOn f (Ioi (2 : ℝ))) (continuous : ContinuousOn f (Ioi (2 : ℝ)))
    {r : ℝ} (hr : 2 < r) : HasDerivAt (exteriorPrimitive f) (f r) r := by
  let f₀ := (Ioi (2 : ℝ)).indicator f
  have h : Integrable f₀ := (integrable_indicator_iff measurableSet_Ioi).mpr integrable
  have localEq : f =ᶠ[𝓝 r] f₀ := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (indicator_of_mem ht _).symm
  have continuous₀ := (continuous.continuousAt (Ioi_mem_nhds hr)).congr localEq
  have derivative := intervalIntegral.integral_hasDerivAt_right (a := 2)
    (h.intervalIntegrable : IntervalIntegrable f₀ volume 2 r)
    h.aestronglyMeasurable.stronglyMeasurableAtFilter continuous₀
  rw [show f₀ r = f r from indicator_of_mem (show r ∈ Ioi (2 : ℝ) from hr) _] at derivative
  exact derivative

private theorem exteriorPrimitive_horizon {f : ℝ → ℂ} (h : IntegrableOn f (Ioi (2 : ℝ))) :
    Tendsto (exteriorPrimitive f) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
  have integrable := (integrable_indicator_iff measurableSet_Ioi).mpr h
  have continuous : Continuous (exteriorPrimitive f) :=
    intervalIntegral.continuous_primitive (fun _ _ => integrable.intervalIntegrable) 2
  have at2 : Tendsto (exteriorPrimitive f) (𝓝 (2 : ℝ)) (𝓝 (exteriorPrimitive f 2)) :=
    continuous.continuousAt.tendsto
  simpa only [exteriorPrimitive,intervalIntegral.integral_same] using
    at2.mono_left (nhdsWithin_le_nhds (s := Ioi (2 : ℝ)))

private theorem exteriorPrimitive_infinity {f : ℝ → ℂ} (h : IntegrableOn f (Ioi (2 : ℝ))) :
    Tendsto (exteriorPrimitive f) atTop (𝓝 (∫ x in Ioi (2 : ℝ), f x)) := by
  let f₀ := (Ioi (2 : ℝ)).indicator f
  have h₀ : Integrable f₀ := (integrable_indicator_iff measurableSet_Ioi).mpr h
  have eq : (∫ x in Ioi (2 : ℝ), f₀ x) = ∫ x in Ioi (2 : ℝ), f x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact indicator_of_mem hx _
  have limit := intervalIntegral_tendsto_integral_Ioi (f := f₀) 2 h₀.integrableOn tendsto_id
  rw [eq] at limit
  exact limit

private theorem variable_modes {l : Filter ℝ} {w : ℂ}
    {u du v dv a b : ℝ → ℂ} {ui uo vi vo a₀ b₀ : ℂ}
    (uModes : RadialModeLimits l w u du ui uo) (vModes : RadialModeLimits l w v dv vi vo)
    (aa : Tendsto a l (𝓝 a₀)) (bb : Tendsto b l (𝓝 b₀)) :
    RadialModeLimits l w (fun r => u r*a r+v r*b r) (fun r => du r*a r+dv r*b r)
      (ui*a₀+vi*b₀) (uo*a₀+vo*b₀) := by
  constructor
  · apply ((uModes.incoming.mul aa).add (vModes.incoming.mul bb)).congr
    intro r
    simp only [incomingMode,div_eq_mul_inv]
    ring
  · apply ((uModes.outgoing.mul aa).add (vModes.outgoing.mul bb)).congr
    intro r
    simp only [outgoingMode,div_eq_mul_inv]
    ring

/-- Integrating the two Green weights constructs the unique real-frequency
retarded field. The outgoing amplitude is the full horizon-wave integral
divided by the Wronskian and the unit-horizon incident amplitude. -/
theorem retarded_green_exists (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) (S : ℝ → ℂ)
    (continuous : ContinuousOn S (Ioi (2 : ℝ)))
    (inner : IntegrableOn (fun x => u.value x*S x/radiusLapse x) (Ioi (2 : ℝ)))
    (outer : IntegrableOn (fun x => u.outgoingCombination (u.value x)*S x/radiusLapse x) (Ioi (2 : ℝ))) :
    let A := (∫ x in Ioi (2 : ℝ), u.value x*S x/radiusLapse x)/(2*w*u.incoming)
    let V := rwPotential w (angularEigenvalue n)
    ∃ p dp : ℝ → ℂ, RadialEquation radiusLapse V S p dp ∧ RetardedBoundary w p dp A ∧
      ∀ (q dq : ℝ → ℂ) (out : ℂ), RadialEquation radiusLapse V S q dq →
        RetardedBoundary w q dq out → (∀ r : ℝ, 2 < r → p r = q r ∧ dp r = dq r) ∧ A = out := by
  dsimp only
  let v := u.outgoingCombination ∘ u.value
  let dv := u.outgoingCombination ∘ u.jet
  let F := fun x => u.value x*S x/radiusLapse x
  let G := fun x => v x*S x/radiusLapse x
  let totalF := ∫ x in Ioi (2 : ℝ), F x
  let totalG := ∫ x in Ioi (2 : ℝ), G x
  let a := fun r => (totalG-exteriorPrimitive G r)/(2*w)
  let b := fun r => exteriorPrimitive F r/(2*w)
  let p := fun r => u.value r*a r+v r*b r
  let dp := fun r => u.jet r*a r+dv r*b r
  let V := rwPotential w (angularEigenvalue n)
  obtain ⟨vEq,vI,W⟩ := outgoing_partner w n hw wi u
  have hLapse : ContinuousOn radiusLapse (Ioi (2 : ℝ)) := by
    unfold radiusLapse
    have cast : ContinuousOn (fun r : ℝ => (r : ℂ)) (Ioi (2 : ℝ)) := Complex.continuous_ofReal.continuousOn
    exact (cast.sub continuousOn_const).div cast (fun r hr =>
      Complex.ofReal_ne_zero.mpr (show r ≠ 0 from (lt_trans (by norm_num) hr).ne'))
  have waveContinuous {x dx : ℝ → ℂ} (hx : RadialEquation radiusLapse V 0 x dx) :
      ContinuousOn x (Ioi (2 : ℝ)) := fun r hr => (hx.value r hr).continuousAt.continuousWithinAt
  have fContinuous : ContinuousOn F (Ioi (2 : ℝ)) :=
    ((waveContinuous u.equation).mul continuous).div hLapse (fun _ hr => exterior_lapse_nonzero hr)
  have gContinuous : ContinuousOn G (Ioi (2 : ℝ)) :=
    ((waveContinuous vEq).mul continuous).div hLapse (fun _ hr => exterior_lapse_nonzero hr)
  have da (r : ℝ) (hr : 2 < r) : HasDerivAt a (-G r/(2*w)) r :=
    ((exteriorPrimitive_deriv outer gContinuous hr).const_sub totalG).div_const (2*w)
  have db (r : ℝ) (hr : 2 < r) : HasDerivAt b (F r/(2*w)) r :=
    (exteriorPrimitive_deriv inner fContinuous hr).div_const (2*w)
  have equation : RadialEquation radiusLapse V S p dp := by
    constructor <;> intro r hr
    · apply (((u.equation.value r hr).mul (da r hr)).add ((vEq.value r hr).mul (db r hr))).congr_deriv
      simp only [dp,F,G,div_eq_mul_inv]
      ring
    · apply (((u.equation.jet r hr).mul (da r hr)).add ((vEq.jet r hr).mul (db r hr))).congr_deriv
      have wr : u.value r*dv r-v r*u.jet r = 2*w := W r hr
      simp only [Pi.zero_apply,add_zero,p,F,G]
      field_simp [hw,exterior_lapse_nonzero hr]
      linear_combination (S r)*wr
  have uH := SchwarzschildMixtures.Strain.normalized_horizon_modes w (angularEigenvalue n) 1
    hw wi u.value u.jet u.horizon u.equation.value
  let c := conj u.outgoing/u.incoming
  have conjH := conjugate_mode_limits _ w wi realTortoise _ _ 1 0 uH
  have partnerH := radial_mode_limits_sub_scaled c conjH uH
  simp only [map_zero,map_one,mul_one,zero_sub,mul_zero,sub_zero] at partnerH
  have aH : Tendsto a (𝓝[>] (2 : ℝ)) (𝓝 (totalG/(2*w))) := by
    simpa only [a,sub_zero] using ((exteriorPrimitive_horizon (f := G) outer).const_sub totalG).div_const (2*w)
  have bH : Tendsto b (𝓝[>] (2 : ℝ)) (𝓝 0) := by
    simpa only [zero_div] using (exteriorPrimitive_horizon inner).div_const (2*w)
  have aI : Tendsto a atTop (𝓝 0) := by
    simpa only [a,totalG,sub_self,zero_div] using
      ((exteriorPrimitive_infinity (f := G) outer).const_sub totalG).div_const (2*w)
  have bI : Tendsto b atTop (𝓝 (totalF/(2*w))) := (exteriorPrimitive_infinity inner).div_const (2*w)
  have vH : RadialModeLimits (𝓝[>] (2 : ℝ)) w v dv (-c) 1 := partnerH
  have boundary : RetardedBoundary w p dp (totalF/(2*w*u.incoming)) := by
    constructor
    · have limits := variable_modes uH vH aH bH
      exact ⟨totalG/(2*w),by simpa only [mul_zero,zero_mul,one_mul,add_zero] using limits⟩
    · have limits := variable_modes u.infinity vI aI bI
      have amplitude : (1/u.incoming)*(totalF/(2*w)) = totalF/(2*w*u.incoming) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      simpa only [p,dp,v,dv,mul_zero,zero_mul,add_zero,zero_add,amplitude] using limits
  have flux := ingoing_scattering_flux w hw wi n 1 u
  have uin := nonzero_incident_amplitude flux (by norm_num : (1:ℂ) ≠ 0)
  exact ⟨p,dp,equation,boundary,fun _ _ _ qEq qBoundary =>
    retarded_solution_unique w (angularEigenvalue n) hw wi u uin equation qEq boundary qBoundary⟩

#print axioms retarded_green_exists

end
end SchwarzschildLaurent.LinearWave
