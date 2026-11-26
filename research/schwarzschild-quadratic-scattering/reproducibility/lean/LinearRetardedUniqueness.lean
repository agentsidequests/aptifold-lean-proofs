import LinearScatteringData

/-! Uniqueness for the real-frequency Regge–Wheeler radiation problem.
The endpoint limits refer to the field and its tortoise derivative. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set SchwarzschildLaurent.Outgoing SchwarzschildMixtures
open scoped Topology

noncomputable section

abbrev RadialModeLimits (l : Filter ℝ) (w : ℂ) (v dv : ℝ → ℂ) (ain aout : ℂ) : Prop :=
  ModeLimits l w (incomingCarrier w) (outgoingCarrier w) v dv ain aout

structure RetardedBoundary (w : ℂ) (v dv : ℝ → ℂ) (aout : ℂ) : Prop where
  horizon : ∃ t, RadialModeLimits (𝓝[>] (2 : ℝ)) w v dv t 0
  infinity : RadialModeLimits atTop w v dv 0 aout

theorem radial_equation_sub_scaled {f V S T p dp u du : ℝ → ℂ} (c : ℂ)
    (hp : RadialEquation f V S p dp) (hu : RadialEquation f V T u du) :
    RadialEquation f V (fun r => S r-c*T r) (fun r => p r-c*u r) (fun r => dp r-c*du r) := by
  constructor <;> intro r hr
  · apply ((hp.value r hr).sub ((hu.value r hr).const_mul c)).congr_deriv
    simp only [div_eq_mul_inv]
    ring
  · apply ((hp.jet r hr).sub ((hu.jet r hr).const_mul c)).congr_deriv
    simp only [div_eq_mul_inv]
    ring

theorem radial_mode_limits_sub_scaled {l : Filter ℝ} {w : ℂ} {p dp u du : ℝ → ℂ}
    {pin pout uin uout : ℂ} (c : ℂ)
    (hp : RadialModeLimits l w p dp pin pout) (hu : RadialModeLimits l w u du uin uout) :
    RadialModeLimits l w (fun r => p r-c*u r) (fun r => dp r-c*du r) (pin-c*uin) (pout-c*uout) := by
  constructor
  · apply (hp.incoming.sub (hu.incoming.const_mul c)).congr
    intro r
    simp only [incomingMode,div_eq_mul_inv]
    ring
  · apply (hp.outgoing.sub (hu.outgoing.const_mul c)).congr
    intro r
    simp only [outgoingMode,div_eq_mul_inv]
    ring

private theorem reverse_frequency_modes {l : Filter ℝ} {w : ℂ} {v dv : ℝ → ℂ} {a b : ℂ}
    (h : RadialModeLimits l (-w) v dv a b) : RadialModeLimits l w v dv b a := by
  refine ⟨h.outgoing.congr fun r => ?_,h.incoming.congr fun r => ?_⟩
  · simp [incomingMode,outgoingMode,incomingCarrier,outgoingCarrier,sub_eq_add_neg,div_neg]
  · simp [incomingMode,outgoingMode,incomingCarrier,outgoingCarrier,sub_eq_add_neg,div_neg]

theorem current_from_horizon {w L : ℂ} (hw : w ≠ 0) {u du v dv : ℝ → ℂ}
    (hu : RadialEquation radiusLapse (rwPotential w L) 0 u du)
    (hv : RadialEquation radiusLapse (rwPotential w L) 0 v dv)
    {a b c d : ℂ} (uh : RadialModeLimits (𝓝[>] (2 : ℝ)) w u du a b)
    (vh : RadialModeLimits (𝓝[>] (2 : ℝ)) w v dv c d) {r : ℝ} (hr : 2 < r) :
    radialCurrent u du v dv r = 2*w*(a*d-b*c) := by
  have limit := current_of_mode_limits (𝓝[>] (2 : ℝ)) w hw _ _ u du v dv
    (fun s => opposite_phases w (realTortoise s)) a b c d uh vh
  have constant : Tendsto (radialCurrent u du v dv) (𝓝[>] (2 : ℝ))
      (𝓝 (radialCurrent u du v dv r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have integral := green_integral_on_interval radiusLapse (rwPotential w L) 0 u du v dv hu hv
      hr (show 2 < s from hs) (by simp)
    exact (sub_eq_zero.mp (by simpa using integral.symm)).symm
  exact tendsto_nhds_unique constant limit

/-- A homogeneous solution with zero outgoing horizon amplitude is its
ingoing horizon amplitude times the normalized ingoing wave. Two
opposite-phase solutions give a nonzero determinant at every radius. -/
theorem ingoing_homogeneous_proportional (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L 1) {v dv : ℝ → ℂ} {t : ℂ}
    (eq : RadialEquation radiusLapse (rwPotential w L) 0 v dv)
    (horizon : RadialModeLimits (𝓝[>] (2 : ℝ)) w v dv t 0) :
    ∀ r : ℝ, 2 < r → v r = t*u.value r ∧ dv r = t*u.jet r := by
  obtain ⟨back⟩ := exists_ingoing_scattering_wave (-w) L 1 (neg_ne_zero.mpr hw) (by simp [wi])
  have same : rwPotential (-w) L = rwPotential w L := by
    funext r
    simp [rwPotential]
  have backEq := back.equation
  rw [same] at backEq
  have uH : RadialModeLimits (𝓝[>] (2 : ℝ)) w u.value u.jet 1 0 :=
    SchwarzschildMixtures.Strain.normalized_horizon_modes w L 1 hw wi _ _ u.horizon u.equation.value
  have backH : RadialModeLimits (𝓝[>] (2 : ℝ)) w back.value back.jet 0 1 :=
    reverse_frequency_modes (SchwarzschildMixtures.Strain.normalized_horizon_modes (-w) L 1
      (neg_ne_zero.mpr hw) (by simp [wi]) _ _ back.horizon back.equation.value)
  intro r hr
  let W := radialCurrent u.value u.jet back.value back.jet r
  have det : W = 2*w := by
    simpa using current_from_horizon hw u.equation backEq uH backH hr
  have hdet : W ≠ 0 := det.trans_ne (mul_ne_zero (by norm_num) hw)
  have vu : radialCurrent u.value u.jet v dv r = 0 := by
    simpa using current_from_horizon hw u.equation eq uH horizon hr
  have vb : radialCurrent back.value back.jet v dv r = -(2*w*t) := by
    simpa [mul_neg] using current_from_horizon hw backEq eq backH horizon hr
  have values : W*(v r-t*u.value r) = 0 := by
    unfold W radialCurrent current at det vu vb ⊢
    linear_combination back.value r*vu-u.value r*vb-t*u.value r*det
  have jets : W*(dv r-t*u.jet r) = 0 := by
    unfold W radialCurrent current at det vu vb ⊢
    linear_combination back.jet r*vu-u.jet r*vb-t*u.jet r*det
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp values).resolve_left hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp jets).resolve_left hdet)⟩

/-- The same regularized source and the retarded boundary conditions
determine the exterior field, its derivative and the outgoing amplitude. -/
theorem retarded_solution_unique (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w L 1) (uin : u.incoming ≠ 0)
    {S p dp v dv : ℝ → ℂ} {q₁ q₂ : ℂ}
    (pEq : RadialEquation radiusLapse (rwPotential w L) S p dp)
    (vEq : RadialEquation radiusLapse (rwPotential w L) S v dv)
    (pBC : RetardedBoundary w p dp q₁) (vBC : RetardedBoundary w v dv q₂) :
    (∀ r : ℝ, 2 < r → p r = v r ∧ dp r = dv r) ∧ q₁ = q₂ := by
  let y := fun r => p r-v r
  let dy := fun r => dp r-dv r
  obtain ⟨a,pa⟩ := pBC.horizon
  obtain ⟨b,vb⟩ := vBC.horizon
  have difference : RadialEquation radiusLapse (rwPotential w L) 0 y dy := by
    change RadialEquation radiusLapse (rwPotential w L) (fun _ => 0) y dy
    simpa [y,dy] using radial_equation_sub_scaled 1 pEq vEq
  have horizon : RadialModeLimits (𝓝[>] (2 : ℝ)) w y dy (a-b) 0 := by
    simpa [y,dy] using radial_mode_limits_sub_scaled 1 pa vb
  have infinity : RadialModeLimits atTop w y dy 0 (q₁-q₂) := by
    simpa [y,dy] using radial_mode_limits_sub_scaled 1 pBC.infinity vBC.infinity
  have proportional := ingoing_homogeneous_proportional w L hw wi u difference horizon
  have predicted : Tendsto (fun r => incomingMode w (outgoingCarrier w r) (y r) (dy r)) atTop
      (𝓝 ((a-b)*u.incoming)) := by
    apply (u.infinity.incoming.const_mul (a-b)).congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
    obtain ⟨value,jet⟩ := proportional r hr
    rw [value,jet]
    simp only [incomingMode,div_eq_mul_inv]
    ring
  have zero := (mul_eq_zero.mp (tendsto_nhds_unique predicted infinity.incoming)).resolve_right uin
  have vanish (r : ℝ) (hr : 2 < r) : y r = 0 ∧ dy r = 0 := by
    simpa only [zero,zero_mul] using proportional r hr
  have outgoing_zero : Tendsto (fun r => outgoingMode w (incomingCarrier w r) (y r) (dy r))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
    simp [outgoingMode,(vanish r hr).1,(vanish r hr).2]
  exact ⟨fun r hr => ⟨sub_eq_zero.mp (vanish r hr).1,sub_eq_zero.mp (vanish r hr).2⟩,
    sub_eq_zero.mp (tendsto_nhds_unique infinity.outgoing outgoing_zero)⟩

#print axioms ingoing_homogeneous_proportional
#print axioms retarded_solution_unique

end
end SchwarzschildLaurent.LinearWave
