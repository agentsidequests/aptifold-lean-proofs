import LowFrequencyHorizonData
import RetardedScattering

/-! Non-cancellation for the actual retarded strain. The low-frequency
parent reflection bound follows from the horizon series and the barrier. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set
open scoped Topology
open SchwarzschildLaurent.Outgoing (incomingMode outgoingMode)
open SchwarzschildMixtures.Strain

noncomputable section

def softIncidenceConstant (n : ℕ) : ℝ :=
  (horizonSeedDistance ((n:ℝ)*(n+1))/100/8)*Real.exp (-2*((n:ℝ)*(n+1)+3))

theorem soft_incidence_constant_positive (n : ℕ) : 0 < softIncidenceConstant n := by
  have d := (horizon_seed_distance_properties (show 0 ≤ (n:ℝ)*(n+1) by positivity)).2.1
  unfold softIncidenceConstant
  positivity

theorem unit_horizon_soft_incidence (n : ℕ) (hn : 2 ≤ n) {omega : ℝ} (wo : 0 < omega)
    (small : omega ≤ 1/(24*(100+4*((n:ℝ)*(n+1)))))
    (parent : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1) :
    softIncidenceConstant n/omega^2 ≤ ‖parent.incoming‖ := by
  have d := (horizon_seed_distance_properties (show 0 ≤ (n:ℝ)*(n+1) by positivity)).2.1
  have w8 : omega ≤ 1/8 := small.trans
    ((div_le_iff₀ (by positivity : 0 < 24*(100+4*((n:ℝ)*(n+1))))).2
      (by linarith [show 0 ≤ (n:ℝ)*(n+1) by positivity]))
  obtain ⟨rot,unit,hv,hj⟩ := positive_four_mass_seeds n hn wo small parent
  exact soft_incidence_from_square_seed n hn wo w8 (div_pos d (by norm_num)) parent rot unit hv hj

theorem unit_horizon_soft_absorption (n : ℕ) (hn : 2 ≤ n) {omega : ℝ} (wo : 0 < omega)
    (small : omega ≤ 1/(24*(100+4*((n:ℝ)*(n+1)))))
    (parent : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) 1) :
    1-‖parent.outgoing/parent.incoming‖^2 ≤ omega^4/(softIncidenceConstant n)^2 := by
  let A := softIncidenceConstant n
  have A0 : 0 < A := soft_incidence_constant_positive n
  have k0 : frequencyParameter omega ≠ 0 :=
    mul_ne_zero (by exact_mod_cast wo.ne') Complex.I_ne_zero
  have ki : (frequencyParameter omega).re = 0 := by simp [frequencyParameter]
  have bound := unit_horizon_soft_incidence n hn wo small parent
  have positive : 0 < A/omega^2 := div_pos A0 (sq_pos_of_pos wo)
  have q := (sq_le_sq₀ positive.le (norm_nonneg _)).2 bound
  rw [unit_horizon_reflected_fraction _ n k0 ki parent]
  calc
    _ = 1/‖parent.incoming‖^2 := by ring
    _ ≤ 1/(A/omega^2)^2 := one_div_le_one_div_of_le (sq_pos_of_pos positive) q
    _ = _ := by
      change 1/(A/omega^2)^2 = omega^4/A^2
      field_simp [A0.ne',wo.ne']

/-- The two scattering amplitudes rescale by the horizon normalization. -/
theorem ingoing_amplitudes_from_unit_horizon (w L : ℂ) (hw : w ≠ 0) (wi : w.re = 0)
    (base : IngoingWaveData w L 1) (a : ℂ) (ref : IngoingWaveData w L a) :
    ref.incoming = a*base.incoming ∧ ref.outgoing = a*base.outgoing := by
  have hm := normalized_horizon_modes w L a hw wi ref.value ref.jet ref.horizon ref.equation.value
  have same := ingoing_homogeneous_proportional w L hw wi base ref.equation hm
  have incoming : Tendsto (fun r => incomingMode w (outgoingCarrier w r) (ref.value r) (ref.jet r))
      atTop (𝓝 (a*base.incoming)) := by
    apply (base.infinity.incoming.const_mul a).congr'
    filter_upwards [eventually_gt_atTop (2:ℝ)] with r hr
    rw [(same r hr).1,(same r hr).2]
    unfold incomingMode
    ring
  have outgoing : Tendsto (fun r => outgoingMode w (incomingCarrier w r) (ref.value r) (ref.jet r))
      atTop (𝓝 (a*base.outgoing)) := by
    apply (base.infinity.outgoing.const_mul a).congr'
    filter_upwards [eventually_gt_atTop (2:ℝ)] with r hr
    rw [(same r hr).1,(same r hr).2]
    unfold outgoingMode
    ring
  exact ⟨tendsto_nhds_unique ref.infinity.incoming incoming,
    tendsto_nhds_unique ref.infinity.outgoing outgoing⟩

/-- The low-frequency bound holds for the printed retarded strain from
every physically normalized source in the second admitted mixture. -/
theorem second_retarded_strain_soft_floor (n : ℕ) (hn : 2 ≤ n) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
      ∀ omega ∈ Ioo 0 ε, ∀ a : ℂ,
        ∀ parent : IngoingWaveData (frequencyParameter omega) (angularEigenvalue n) a,
        ∀ daughter : IngoingWaveData (2*frequencyParameter omega) (angularEigenvalue (2*n)) 1,
          parent.incoming = parentAlpha (frequencyParameter omega) n →
          c*omega^3 ≤ ‖printedResponse true (frequencyParameter omega) n
            parent.outgoing (daughter.outgoing/daughter.incoming)‖ := by
  let A := softIncidenceConstant n
  let δ : ℝ := 1/(24*(100+4*((n:ℝ)*(n+1))))
  have δp : 0 < δ := by dsimp only [δ]; positivity
  have A0 : 0 < A := soft_incidence_constant_positive n
  have freq : Tendsto (fun w : ℝ => w) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have loss : Tendsto (fun w => (w^4/A^2)/w^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have simple : Tendsto (fun w => w^2/A^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0),zero_div] using (freq.pow 2).div_const (A^2)
    apply simple.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    have w0 : w ≠ 0 := (show 0 < w from hw).ne'
    field_simp [A0.ne',w0]
  obtain ⟨c,cp,h⟩ := second_response_soft_floor_of_loss_bound n hn (fun w => w^4/A^2) loss
  obtain ⟨b,b0,band⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  refine ⟨c,min b δ,cp,lt_min b0 δp,?_⟩
  intro omega hw a parent daughter incident
  have wo : 0 < omega := hw.1
  have small : omega ≤ δ := (hw.2.trans_le (min_le_right _ _)).le
  let k := frequencyParameter omega
  have k0 : k ≠ 0 := mul_ne_zero (by exact_mod_cast wo.ne') Complex.I_ne_zero
  have ki : k.re = 0 := by simp [k,frequencyParameter]
  have dk0 : 2*k ≠ 0 := mul_ne_zero (by norm_num) k0
  have dki : (2*k).re = 0 := by simp [Complex.mul_re,ki]
  obtain ⟨base⟩ := exists_ingoing_scattering_wave k (angularEigenvalue n) 1 k0 ki
  obtain ⟨ain,aout⟩ := ingoing_amplitudes_from_unit_horizon k _ k0 ki base a parent
  have nIn : ‖parent.incoming‖ = 1 := by rw [incident,parent_incidence_unit n hn k ki]
  have nonzero : parent.incoming ≠ 0 := norm_ne_zero_iff.mp (by rw [nIn]; norm_num)
  have base0 : base.incoming ≠ 0 := fun eq => nonzero (by simp [ain,eq])
  have rEq : parent.incoming*(base.outgoing/base.incoming) = parent.outgoing := by
    rw [ain,aout]
    field_simp [base0]
  have nOut : ‖parent.outgoing‖ = ‖base.outgoing/base.incoming‖ := by
    rw [← rEq,norm_mul,nIn,one_mul]
  have absorbed := unit_horizon_soft_absorption n hn wo small base
  have pd : ‖daughter.outgoing/daughter.incoming‖ ≤ 1 :=
    (ingoing_amplitude_gains (2*k) (2*n) dk0 dki daughter).2.le
  exact band ⟨wo,hw.2.trans_le (min_le_left _ _)⟩ _ _ (by rw [nOut]; exact absorbed) pd

#print axioms unit_horizon_soft_incidence
#print axioms unit_horizon_soft_absorption
#print axioms ingoing_amplitudes_from_unit_horizon
#print axioms second_retarded_strain_soft_floor

end
end SchwarzschildLaurent.LinearWave
