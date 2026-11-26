import OutgoingRadiusLimits

/-! Conserved real-frequency flux. The right-horizon normalization
and the infinity amplitudes refer to the same homogeneous wave. -/
namespace SchwarzschildLaurent.Outgoing

open Filter Set MeasureTheory ComplexConjugate
open scoped Topology Interval

noncomputable section

theorem imaginary_conjugate {w : ℂ} (hi : w.re = 0) : conj w = -w := by
  apply Complex.ext <;> simp [hi]

private theorem conjugate_phase (w : ℂ) (hi : w.re = 0) (x : ℝ) :
    conj (phase w x) = phase (-w) x := by
  simp only [phase,← Complex.exp_conj,map_mul,Complex.conj_ofReal,imaginary_conjugate hi]

theorem lapse_is_real (r : ℝ) : conj (radiusLapse r) = radiusLapse r := by
  simp [radiusLapse,map_ofNat]

theorem rw_potential_is_real (w : ℂ) (hi : w.re = 0) (L : ℝ) (r : ℝ) :
    conj (rwPotential w (L : ℂ) r) = rwPotential w (L : ℂ) r := by
  simp [rwPotential,imaginary_conjugate hi,lapse_is_real,map_ofNat]

theorem conjugate_radial_equation (f V u du : ℝ → ℂ)
    (hf : ∀ r, conj (f r) = f r) (hv : ∀ r, conj (V r) = V r)
    (eq : RadialEquation f V 0 u du) :
    RadialEquation f V 0 (fun r => conj (u r)) (fun r => conj (du r)) := by
  constructor <;> intro r hr
  · have d := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r (eq.value r hr)
    change HasDerivAt (fun s => conj (u s)) (conj (du r/f r)) r at d
    simpa [hf] using d
  · have d := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r (eq.jet r hr)
    change HasDerivAt (fun s => conj (du s)) (conj ((V r*u r+(0 : ℝ → ℂ) r)/f r)) r at d
    simpa [hf,hv] using d

theorem conjugate_mode_limits (l : Filter ℝ) (w : ℂ) (hi : w.re = 0)
    (x : ℝ → ℝ) (u du : ℝ → ℂ) (ai ao : ℂ)
    (hm : ModeLimits l w (fun r => phase (-w) (x r)) (fun r => phase w (x r)) u du ai ao) :
    ModeLimits l w (fun r => phase (-w) (x r)) (fun r => phase w (x r))
      (fun r => conj (u r)) (fun r => conj (du r)) (conj ao) (conj ai) := by
  have fromOut := Complex.continuous_conj.continuousAt.tendsto.comp hm.outgoing
  have fromIn := Complex.continuous_conj.continuousAt.tendsto.comp hm.incoming
  have swap := conjugate_phase (-w) (by simp [hi])
  refine ⟨fromOut.congr fun r => ?_,fromIn.congr fun r => ?_⟩
  · simp [incomingMode,outgoingMode,swap,imaginary_conjugate hi,map_ofNat,div_neg_eq_neg_div,sub_eq_add_neg]
  · simp [incomingMode,outgoingMode,conjugate_phase w hi,imaginary_conjugate hi,map_ofNat,
      div_neg_eq_neg_div,sub_eq_add_neg]

private theorem horizon_modes (w : ℂ) (hw : w ≠ 0) (m p H dH : ℂ) (hmp : m*p = 1) :
    incomingMode w p (m*H) (m*(dH-w*H)) = H-dH/(2*w) ∧
    outgoingMode w m (m*H) (m*(dH-w*H)) = m^2*(dH/(2*w)) := by
  unfold incomingMode outgoingMode
  constructor
  · field_simp [hw]
    linear_combination (2*w*H-dH)*hmp
  · field_simp [hw] <;> ring

theorem ingoing_analytic_mode_limits (w : ℂ) (hw : w ≠ 0) (hi : w.re = 0)
    (x : ℝ → ℝ) (u du : ℝ → ℂ) (H : ℂ → ℂ) (ah : AnalyticAt ℂ H 2)
    (carrier : ∀ r, 2 < r → HasDerivAt (fun a => phase (-w) (x a))
      (-w*phase (-w) (x r)/radiusLapse r) r)
    (value : ∀ᶠ r in 𝓝[>] (2 : ℝ), u r = phase (-w) (x r)*H (r : ℂ))
    (jet : ∀ r, 2 < r → HasDerivAt u (du r/radiusLapse r) r) :
    ModeLimits (𝓝[>] (2 : ℝ)) w (fun r => phase (-w) (x r)) (fun r => phase w (x r)) u du (H 2) 0 := by
  obtain ⟨h,dh⟩ := horizon_envelope_limits H ah
  have i := h.sub (dh.div_const (2*w))
  simp only [zero_div,sub_zero] at i
  have o := unit_mul_zero (c := fun r => phase (-w) (x r)^2)
    (fun r => by simp [norm_pow,phase_norm,hi]) (by simpa only [zero_div] using dh.div_const (2*w))
  have eq := ingoing_exterior_jet w _ u du H ah carrier value jet
  refine ⟨i.congr' ?_,o.congr' ?_⟩
  · filter_upwards [value,eq] with r h₁ h₂
    rw [h₁,h₂]
    exact (horizon_modes w hw _ _ _ _ (opposite_phases w (x r))).1.symm
  · filter_upwards [value,eq] with r h₁ h₂
    rw [h₁,h₂]
    exact (horizon_modes w hw _ _ _ _ (opposite_phases w (x r))).2.symm

theorem flux_balance (w : ℂ) (hw : w ≠ 0) (hi : w.re = 0) (x : ℝ → ℝ)
    (f V u du : ℝ → ℂ) (hf : ∀ r, conj (f r) = f r) (hv : ∀ r, conj (V r) = V r)
    (equation : RadialEquation f V 0 u du) (ai ao t : ℂ)
    (infinity : ModeLimits atTop w (fun r => phase (-w) (x r)) (fun r => phase w (x r)) u du ai ao)
    (horizon : ModeLimits (𝓝[>] (2 : ℝ)) w
      (fun r => phase (-w) (x r)) (fun r => phase w (x r)) u du t 0) :
    Complex.normSq ai = Complex.normSq ao + Complex.normSq t := by
  let U := fun r => conj (u r)
  let dU := fun r => conj (du r)
  have adjoint := conjugate_radial_equation f V u du hf hv equation
  have constant : ∀ r, 2 < r → radialCurrent U dU u du r = radialCurrent U dU u du 3 := by
    intro r hr
    have finite := green_integral_on_interval f V 0 U dU u du adjoint equation (by norm_num : 2 < (3:ℝ)) hr
      (by simp)
    apply sub_eq_zero.mp
    simpa using finite.symm
  have conjugated₁ := conjugate_mode_limits _ w hi x u du ai ao infinity
  have conjugated₂ := conjugate_mode_limits _ w hi x u du t 0 horizon
  have h₁ := current_of_mode_limits atTop w hw _ _ U dU u du
    (fun r => opposite_phases w (x r)) _ _ _ _ conjugated₁ infinity
  have h₂ := current_of_mode_limits (𝓝[>] (2 : ℝ)) w hw _ _ U dU u du
    (fun r => opposite_phases w (x r)) _ _ _ _ conjugated₂ horizon
  have c₁ : Tendsto (radialCurrent U dU u du) atTop (𝓝 (radialCurrent U dU u du 3)) :=
    tendsto_const_nhds.congr' ((eventually_gt_atTop (2:ℝ)).mono fun r hr => (constant r hr).symm)
  have rightSide : ∀ᶠ r : ℝ in 𝓝[>] (2 : ℝ), 2 < r := self_mem_nhdsWithin
  have c₂ : Tendsto (radialCurrent U dU u du) (𝓝[>] (2 : ℝ)) (𝓝 (radialCurrent U dU u du 3)) :=
    tendsto_const_nhds.congr' (rightSide.mono fun r hr => (constant r hr).symm)
  have equal := (tendsto_nhds_unique h₁ c₁).trans (tendsto_nhds_unique c₂ h₂)
  have cancel := mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hw) equal
  rw [mul_comm (conj ao), mul_comm (conj ai),mul_comm (conj t)] at cancel
  simp only [Complex.mul_conj,map_zero,zero_mul,zero_sub] at cancel
  have real := congrArg Complex.re cancel
  simp only [Complex.sub_re,Complex.neg_re,Complex.ofReal_re] at real
  linarith

theorem nonzero_incident_amplitude {ai ao t : ℂ}
    (flux : Complex.normSq ai = Complex.normSq ao + Complex.normSq t) (ht : t ≠ 0) : ai ≠ 0 := by
  intro h
  rw [h,map_zero] at flux
  have pos := Complex.normSq_pos.2 ht
  have nn := Complex.normSq_nonneg ao
  linarith

#print axioms ingoing_analytic_mode_limits
#print axioms flux_balance
#print axioms nonzero_incident_amplitude

end
end SchwarzschildLaurent.Outgoing
