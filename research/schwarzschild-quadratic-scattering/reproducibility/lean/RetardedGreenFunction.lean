import LinearRetardedUniqueness

/-! The outgoing homogeneous partner and the finite-radius retarded
Green integral at nonzero real frequency. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Set MeasureTheory ComplexConjugate
open SchwarzschildLaurent.Outgoing SchwarzschildMixtures
open scoped Topology Interval

noncomputable section

/-- Apply the same outgoing combination to the wave and to its jet. -/
def IngoingWaveData.outgoingCombination {w L : ℂ} (u : IngoingWaveData w L 1) (z : ℂ) : ℂ :=
  conj z - (conj u.outgoing/u.incoming)*z

/-- The outgoing partner has unit outgoing horizon coefficient and
outgoing infinity coefficient equal to the inverse incident amplitude. -/
theorem outgoing_partner (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) :
    let v := u.outgoingCombination ∘ u.value
    let dv := u.outgoingCombination ∘ u.jet
    RadialEquation radiusLapse (rwPotential w (angularEigenvalue n)) 0 v dv ∧
    RadialModeLimits atTop w v dv 0 (1/u.incoming) ∧
    ∀ r : ℝ, 2 < r → radialCurrent u.value u.jet v dv r = 2*w := by
  let c := conj u.outgoing/u.incoming
  have real (r : ℝ) : conj (rwPotential w (angularEigenvalue n) r) =
      rwPotential w (angularEigenvalue n) r := by
    have h := rw_potential_is_real w wi ((n : ℝ)*(n+1)) r
    push_cast at h
    exact h
  have adjoint := conjugate_radial_equation radiusLapse _ _ _ lapse_is_real real u.equation
  have eq := radial_equation_sub_scaled c adjoint u.equation
  simp only [Pi.zero_apply,mul_zero,sub_zero] at eq
  have uH := SchwarzschildMixtures.Strain.normalized_horizon_modes w (angularEigenvalue n) 1
    hw wi u.value u.jet u.horizon u.equation.value
  have adjointH := conjugate_mode_limits _ w wi realTortoise _ _ 1 0 uH
  have pH := radial_mode_limits_sub_scaled c adjointH uH
  simp only [map_zero,map_one,mul_one,zero_sub,mul_zero,sub_zero] at pH
  have adjointI := conjugate_mode_limits atTop w wi realTortoise _ _ u.incoming u.outgoing u.infinity
  have pI := radial_mode_limits_sub_scaled c adjointI u.infinity
  have flux := ingoing_scattering_flux w hw wi n 1 u
  have uin := nonzero_incident_amplitude flux (by norm_num : (1:ℂ) ≠ 0)
  have cancel : conj u.outgoing-c*u.incoming = 0 := by dsimp only [c]; rw [div_mul_cancel₀ _ uin,sub_self]
  have outgoing : conj u.incoming-c*u.outgoing = 1/u.incoming := by
    apply (eq_div_iff uin).2
    calc
      _ = u.incoming*conj u.incoming-u.outgoing*conj u.outgoing := by
        dsimp only [c]
        field_simp [uin]
      _ = 1 := by
        have h : Complex.normSq u.incoming-Complex.normSq u.outgoing = 1 := by
          simp only [map_one] at flux
          linarith
        rw [Complex.mul_conj,Complex.mul_conj,← Complex.ofReal_sub,h,Complex.ofReal_one]
  rw [cancel,outgoing] at pI
  refine ⟨eq,pI,?_⟩
  intro r hr
  change radialCurrent u.value u.jet (fun x => conj (u.value x)-c*u.value x)
    (fun x => conj (u.jet x)-c*u.jet x) r = 2*w
  simpa only [one_mul,zero_mul,sub_zero,mul_one] using
    current_from_horizon hw u.equation eq uH pH hr

/-- Both entries use tortoise-coordinate source integration, expressed
in areal radius. The second entry uses the jets in the two weights. -/
def greenCutoff (u du v dv S : ℝ → ℂ) (det : ℂ) (r : ℝ) (ab : ℝ × ℝ) : ℂ × ℂ :=
  let left := ∫ x in ab.1..r, u x*S x/radiusLapse x
  let right := ∫ x in r..ab.2, v x*S x/radiusLapse x
  ((v r*left+u r*right)/det,(dv r*left+du r*right)/det)

/-- Exact finite-cutoff corrections, including the sign of each
boundary current and the correction for the tortoise derivative. -/
theorem green_cutoff_identity (V S u du v dv p dp : ℝ → ℂ) (det : ℂ) (nonzero : det ≠ 0)
    (uEq : RadialEquation radiusLapse V 0 u du)
    (vEq : RadialEquation radiusLapse V 0 v dv)
    (pEq : RadialEquation radiusLapse V S p dp)
    {a b r : ℝ} (ha : 2 < a) (hb : 2 < b) (hr : 2 < r)
    (wronskian : radialCurrent u du v dv r = det)
    (left : IntervalIntegrable (fun x => u x*S x/radiusLapse x) volume a r)
    (right : IntervalIntegrable (fun x => v x*S x/radiusLapse x) volume r b) :
    greenCutoff u du v dv S det r (a,b) =
      (p r+(u r*radialCurrent v dv p dp b-v r*radialCurrent u du p dp a)/det,
       dp r+(du r*radialCurrent v dv p dp b-dv r*radialCurrent u du p dp a)/det) := by
  have A := green_integral_on_interval radiusLapse _ _ u du p dp uEq pEq ha hr left
  have B := green_integral_on_interval radiusLapse _ _ v dv p dp vEq pEq hr hb right
  apply Prod.ext
  all_goals
    simp only [greenCutoff,A,B]
    field_simp [nonzero]
    rw [← wronskian]
    unfold radialCurrent current
    ring

/-- The two independent radial cutoffs recover both the full retarded
field and its tortoise derivative at every exterior radius. -/
theorem retarded_green_field_limit (w : ℂ) (n : ℕ) (hw : w ≠ 0) (wi : w.re = 0)
    (u : IngoingWaveData w (angularEigenvalue n) 1) {S p dp : ℝ → ℂ} {q : ℂ}
    (pEq : RadialEquation radiusLapse (rwPotential w (angularEigenvalue n)) S p dp)
    (pBoundary : RetardedBoundary w p dp q)
    (innerIntegrable : ∀ a r : ℝ, 2 < a → 2 < r →
      IntervalIntegrable (fun x => u.value x*S x/radiusLapse x) volume a r)
    (outerIntegrable : ∀ r b : ℝ, 2 < r → 2 < b →
      IntervalIntegrable (fun x => u.outgoingCombination (u.value x)*S x/radiusLapse x) volume r b)
    {r : ℝ} (hr : 2 < r) :
    Tendsto (greenCutoff u.value u.jet (u.outgoingCombination ∘ u.value)
      (u.outgoingCombination ∘ u.jet) S (2*w) r)
      ((𝓝[>] (2 : ℝ)) ×ˢ atTop) (𝓝 (p r,dp r)) := by
  let v := u.outgoingCombination ∘ u.value
  let dv := u.outgoingCombination ∘ u.jet
  have ⟨vEq,vI,W⟩ := outgoing_partner w n hw wi u
  obtain ⟨t,h⟩ := pBoundary.horizon
  have uH := SchwarzschildMixtures.Strain.normalized_horizon_modes w (angularEigenvalue n) 1 hw wi
    u.value u.jet u.horizon u.equation.value
  have lower : Tendsto (fun x => current (u.value x) (u.jet x) (p x) (dp x)) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero,zero_mul,sub_self] using
      current_of_mode_limits _ w hw _ _ u.value u.jet p dp
        (fun s => opposite_phases w (realTortoise s)) 1 0 t 0 uH h
  have upper : Tendsto (fun x => current (v x) (dv x) (p x) (dp x)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,sub_self] using
      current_of_mode_limits atTop w hw _ _ v dv p dp
        (fun s => opposite_phases w (realTortoise s)) 0 (1/u.incoming) 0 q vI pBoundary.infinity
  let cutoffs := (𝓝[>] (2 : ℝ)) ×ˢ (atTop : Filter ℝ)
  have lo : Tendsto (fun ab : ℝ × ℝ => radialCurrent u.value u.jet p dp ab.1) cutoffs (𝓝 0) :=
    lower.comp tendsto_fst
  have hi : Tendsto (fun ab : ℝ × ℝ => radialCurrent v dv p dp ab.2) cutoffs (𝓝 0) :=
    upper.comp tendsto_snd
  have value := ((((hi.const_mul (u.value r)).sub (lo.const_mul (v r))).div_const (2*w))).const_add (p r)
  have jet := ((((hi.const_mul (u.jet r)).sub (lo.const_mul (dv r))).div_const (2*w))).const_add (dp r)
  have limit := value.prodMk_nhds jet
  simp only [mul_zero,sub_zero,zero_div,add_zero] at limit
  apply limit.congr'
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : ∀ᶠ a in 𝓝[>] (2 : ℝ), a ∈ Ioi 2),
    tendsto_snd.eventually (eventually_gt_atTop (2 : ℝ))] with ab ha hb
  exact (green_cutoff_identity _ S u.value u.jet v dv p dp (2*w) (mul_ne_zero (by norm_num) hw)
    u.equation vEq pEq ha hb hr (W r hr) (innerIntegrable _ _ ha hr) (outerIntegrable _ _ hr hb)).symm

#print axioms outgoing_partner
#print axioms green_cutoff_identity
#print axioms retarded_green_field_limit

end
end SchwarzschildLaurent.LinearWave
