import RetardedGreenExistence
import RadialEndpointEstimates

/-! Radiation mode limits give ordinary wave and jet bounds at either
endpoint. The bounds make the Green source weights integrable. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set MeasureTheory SchwarzschildLaurent.Outgoing SchwarzschildLaurent.Exterior
open SchwarzschildMixtures
open scoped Topology

noncomputable section

theorem radial_modes_eventually_bounded {l : Filter ℝ} {w : ℂ} (hw : w ≠ 0) (wi : w.re = 0)
    {u du : ℝ → ℂ} {ai ao : ℂ} (limits : RadialModeLimits l w u du ai ao) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in l, ‖u r‖ ≤ C ∧ ‖du r‖ ≤ C := by
  obtain ⟨a,apos,ha⟩ := eventually_bounded_norm_of_limit limits.incoming
  obtain ⟨b,bpos,hb⟩ := eventually_bounded_norm_of_limit limits.outgoing
  refine ⟨(‖w‖+1)*(a+b),by positivity,?_⟩
  filter_upwards [ha,hb] with r ar br
  let m := incomingCarrier w r
  let p := outgoingCarrier w r
  let I := incomingMode w p (u r) (du r)
  let O := outgoingMode w m (u r) (du r)
  have mnorm : ‖m‖ = 1 := phase_norm (-w) (by simp [wi]) (realTortoise r)
  have pnorm : ‖p‖ = 1 := phase_norm w wi (realTortoise r)
  obtain ⟨value,jet⟩ := reconstruct_modes w m p (u r) (du r) hw (opposite_phases w (realTortoise r))
  have valueBound : ‖u r‖ ≤ a+b := by
    rw [← value]
    change ‖I*m+O*p‖ ≤ a+b
    refine (norm_add_le _ _).trans ?_
    simpa only [norm_mul,mnorm,pnorm,mul_one] using (add_le_add ar br)
  have jetBound : ‖du r‖ ≤ ‖w‖*(a+b) := by
    rw [← jet]
    change ‖w*(O*p-I*m)‖ ≤ ‖w‖*(a+b)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg w)
    simpa only [norm_mul,pnorm,mnorm,mul_one,add_comm] using (add_le_add br ar)
  constructor
  · exact valueBound.trans (by nlinarith [mul_nonneg (norm_nonneg w) (add_nonneg apos.le bpos.le)])
  · exact jetBound.trans (by nlinarith)

theorem ingoing_wave_endpoint_bounds {w L a : ℂ} (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L a) :
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖u.value r‖ ≤ C ∧ ‖u.jet r‖ ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ r in atTop, ‖u.value r‖ ≤ C ∧ ‖u.jet r‖ ≤ C) := by
  have horizon := Strain.normalized_horizon_modes w L a hw wi u.value u.jet u.horizon u.equation.value
  exact ⟨radial_modes_eventually_bounded hw wi horizon,radial_modes_eventually_bounded hw wi u.infinity⟩

theorem outgoing_partner_endpoint_bounds {w L : ℂ} (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L 1) :
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖u.outgoingCombination (u.value r)‖ ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ r in atTop, ‖u.outgoingCombination (u.value r)‖ ≤ C) := by
  have bounds := ingoing_wave_endpoint_bounds hw wi u
  have transfer {l : Filter ℝ} (B : ℝ) (positive : 0 < B)
      (bound : ∀ᶠ r in l, ‖u.value r‖ ≤ B ∧ ‖u.jet r‖ ≤ B) :
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in l, ‖u.outgoingCombination (u.value r)‖ ≤ C := by
    let c := star u.outgoing/u.incoming
    refine ⟨B+‖c‖*B,by positivity,?_⟩
    filter_upwards [bound] with r hr
    change ‖star (u.value r)-c*u.value r‖ ≤ B+‖c‖*B
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul,norm_star]
    exact add_le_add hr.1 (mul_le_mul_of_nonneg_left hr.1 (norm_nonneg c))
  obtain ⟨B,bpos,bound⟩ := bounds.1
  obtain ⟨C,cpos,other⟩ := bounds.2
  exact ⟨transfer B bpos bound,transfer C cpos other⟩

theorem source_weight_integrable (u S : ℝ → ℂ)
    (uc : ContinuousOn u (Ioi (2 : ℝ))) (sc : ContinuousOn S (Ioi (2 : ℝ)))
    (uH : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖u r‖ ≤ C)
    (uI : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in atTop, ‖u r‖ ≤ C)
    (sH : ∃ C : ℝ, ∀ᶠ r in 𝓝[>] (2 : ℝ), ‖S r‖ ≤ C)
    (sI : ∃ C : ℝ, ∀ᶠ r in atTop, ‖S r‖ ≤ C*r^(-2 : ℝ)) :
    IntegrableOn (fun r => u r*S r) (Ioi (2 : ℝ)) := by
  apply integrable_on_exterior_of_endpoint_bounds _ (uc.mul sc)
  · obtain ⟨a,apos,ha⟩ := uH
    obtain ⟨b,hb⟩ := sH
    refine ⟨a*b,?_⟩
    filter_upwards [ha,hb] with r h₁ h₂
    change ‖u r*S r‖ ≤ a*b
    rw [norm_mul]
    exact mul_le_mul h₁ h₂ (norm_nonneg _) apos.le
  · obtain ⟨a,apos,ha⟩ := uI
    obtain ⟨b,hb⟩ := sI
    refine ⟨a*b,?_⟩
    filter_upwards [ha,hb] with r h₁ h₂
    change ‖u r*S r‖ ≤ (a*b)*r^(-2 : ℝ)
    rw [norm_mul,mul_assoc]
    exact mul_le_mul h₁ h₂ (norm_nonneg _) apos.le

#print axioms radial_modes_eventually_bounded
#print axioms ingoing_wave_endpoint_bounds
#print axioms outgoing_partner_endpoint_bounds
#print axioms source_weight_integrable

end
end SchwarzschildLaurent.LinearWave
