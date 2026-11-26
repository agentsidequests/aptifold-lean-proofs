import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! An inverse-square radial bound on the derivative gives a limit in
the amplitude variables and a quantitative inverse-radius remainder. -/
namespace SchwarzschildLaurent.LinearWave

open Filter Metric Set
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An inverse-square generator becomes bounded in the finite
coordinate `t = -1/r`. Completeness gives the missing endpoint. -/
theorem inverse_square_limit [CompleteSpace E] (u du : ℝ → E) (C : ℝ) (hC : 0 ≤ C)
    (d : ∀ r, 2 < r → HasDerivAt u (du r) r)
    (bound : ∀ r, 2 < r → ‖du r‖ ≤ (C/r^2)*‖u r‖) :
    ∃ a : E, Tendsto u atTop (𝓝 a) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ r : ℝ, 3 ≤ r → ‖u r-a‖ ≤ M/r := by
  let start : ℝ := -(1/3)
  let Y := fun t : ℝ => u (-t⁻¹)
  let DY := fun t : ℝ => ((t^2)⁻¹ : ℝ) • du (-t⁻¹)
  have radius {t : ℝ} (ht : t ∈ Ico start 0) : 3 ≤ -t⁻¹ := by
    have pos : 0 < -t := neg_pos.2 ht.2
    have hstart : -(1/3:ℝ) ≤ t := ht.1
    calc
      _ ≤ (1:ℝ)/(-t) := (le_div_iff₀ pos).2 (by linarith)
      _ = _ := by rw [one_div,inv_neg]
  have dyn (t : ℝ) (ht : t ∈ Ico start 0) : HasDerivAt Y (DY t) t := by
    have r : 2 < -t⁻¹ := lt_of_lt_of_le (by norm_num) (radius ht)
    simpa only [Y,DY,neg_neg,Function.comp_def,Pi.neg_apply] using
      (d _ r).scomp t (hasDerivAt_inv ht.2.ne).neg
  have dynBound (t : ℝ) (ht : t ∈ Ico start 0) : ‖DY t‖ ≤ C*‖Y t‖ := by
    have r : 2 < -t⁻¹ := lt_of_lt_of_le (by norm_num) (radius ht)
    have nz : t ≠ 0 := ht.2.ne
    unfold DY
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (t^2)⁻¹)]
    calc
      _ ≤ (t^2)⁻¹*((C/(-t⁻¹)^2)*‖Y t‖) := mul_le_mul_of_nonneg_left (bound _ r) (by positivity)
      _ = _ := by rw [neg_sq,inv_pow,div_inv_eq_mul]; field_simp [nz]
  let N := ‖Y start‖*Real.exp (C*(1/3))
  have magnitude (t : ℝ) (ht : t ∈ Ico start 0) : ‖Y t‖ ≤ N := by
    have admitted : Icc start t ⊆ Ico start 0 := fun r hr => ⟨hr.1,hr.2.trans_lt ht.2⟩
    have cont : ContinuousOn Y (Icc start t) := fun r hr => (dyn r (admitted hr)).continuousAt.continuousWithinAt
    have g := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) cont
      (fun r hr => (dyn r (admitted (Ico_subset_Icc_self hr))).hasDerivWithinAt)
      (le_refl ‖Y start‖)
      (fun r hr => by simpa only [add_zero] using dynBound r (admitted (Ico_subset_Icc_self hr)))
      t ⟨ht.1,le_rfl⟩
    rw [gronwallBound_ε0] at g
    apply g.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.2
    have delta : t-start ≤ 1/3 := by dsimp only [start]; linarith [ht.2]
    exact mul_le_mul_of_nonneg_left delta hC
  let M := C*N
  have m0 : 0 ≤ M := by dsimp only [M,N]; positivity
  have diff_ordered {x y : ℝ} (xI : x ∈ Ico start 0) (yI : y ∈ Ico start 0) (xy : x ≤ y) :
      ‖Y y-Y x‖ ≤ M*(y-x) := by
    have subI : Icc x y ⊆ Ico start 0 := fun r hr => ⟨xI.1.trans hr.1,hr.2.trans_lt yI.2⟩
    exact norm_image_sub_le_of_norm_deriv_le_segment'
      (fun r hr => (dyn r (subI hr)).hasDerivWithinAt)
      (fun r hr => (dynBound _ (subI (Ico_subset_Icc_self hr))).trans
        (mul_le_mul_of_nonneg_left (magnitude _ (subI (Ico_subset_Icc_self hr))) hC))
      y ⟨xy,le_rfl⟩
  have diff {x y : ℝ} (xI : x ∈ Ico start 0) (yI : y ∈ Ico start 0) :
      ‖Y y-Y x‖ ≤ M*|y-x| := by
    rcases le_total x y with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact diff_ordered xI yI h
    · rw [norm_sub_rev,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr h)]
      exact diff_ordered yI xI h
  have smallLeft (ε : ℝ) (εpos : 0 < ε) : Ioo (-ε) 0 ∈ 𝓝[<] (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (neg_lt_zero.2 εpos))] with s hi lo
    exact ⟨lo,hi⟩
  have cauchy : Cauchy (Filter.map Y (𝓝[<] (0:ℝ))) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance,?_⟩
    intro ε epos
    let δ : ℝ := min (1/3) (ε/(M+1))
    have den : 0 < M+1 := by linarith
    have δpos : 0 < δ := lt_min (by norm_num) (div_pos epos den)
    refine ⟨Y '' Ioo (-δ) 0,image_mem_map (smallLeft δ δpos),?_⟩
    intro x hx y hy
    obtain ⟨s,hs,rfl⟩ := hx
    obtain ⟨t,ht,rfl⟩ := hy
    have boundδ : δ ≤ 1/3 := min_le_left _ _
    have si : s ∈ Ico start 0 := ⟨by dsimp only [start]; linarith [hs.1],hs.2⟩
    have ti : t ∈ Ico start 0 := ⟨by dsimp only [start]; linarith [ht.1],ht.2⟩
    have gap : |s-t| ≤ δ := abs_le.2 ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
    rw [dist_eq_norm]
    calc
      _ ≤ M*|s-t| := diff ti si
      _ ≤ M*δ := mul_le_mul_of_nonneg_left gap m0
      _ < (M+1)*δ := mul_lt_mul_of_pos_right (by linarith) δpos
      _ ≤ _ := (le_div_iff₀' den).1 (min_le_right _ _)
  obtain ⟨a,limit⟩ := cauchy_map_iff_exists_tendsto.1 cauchy
  have near : Ico start 0 ∈ 𝓝[<] (0:ℝ) :=
    mem_of_superset (smallLeft (1/3) (by norm_num)) fun _ hx => ⟨hx.1.le,hx.2⟩
  have remainder (t : ℝ) (ht : t ∈ Ico start 0) : ‖Y t-a‖ ≤ M*|t| := by
    have l : Tendsto (fun s => ‖Y t-Y s‖) (𝓝[<] (0:ℝ)) (𝓝 ‖Y t-a‖) :=
      (tendsto_const_nhds.sub limit).norm
    have r : Tendsto (fun s : ℝ => M*|t-s|) (𝓝[<] (0:ℝ)) (𝓝 (M*|t|)) := by
      have side : Tendsto (fun s : ℝ => s) (𝓝[<] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      simpa only [sub_zero] using ((tendsto_const_nhds (x := t)).sub side).abs.const_mul M
    exact le_of_tendsto_of_tendsto l r (mem_of_superset near fun _ hx => diff hx ht)
  have inverse : Tendsto (fun r : ℝ => -r⁻¹) atTop (𝓝[<] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨by simpa only [neg_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg,?_⟩
    exact (eventually_gt_atTop (2:ℝ)).mono fun r hr =>
      show -r⁻¹ < 0 from neg_lt_zero.2 (inv_pos.2 (show 0 < r by linarith))
  refine ⟨a,?_,M,m0,?_⟩
  · simpa only [Function.comp_def,Y,inv_neg,inv_inv,neg_neg] using limit.comp inverse
  · intro r hr
    have pos : 0 < r := by linarith
    have mem : -r⁻¹ ∈ Ico start 0 := by
      refine ⟨?_,neg_lt_zero.2 (inv_pos.2 pos)⟩
      change -(1/3:ℝ) ≤ -r⁻¹
      rw [neg_le_neg_iff,← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hr
    simpa only [Y,inv_neg,inv_inv,neg_neg,abs_neg,abs_of_pos (inv_pos.2 pos),div_eq_mul_inv]
      using remainder _ mem

/-- A finite-radius modal norm gives a lower bound on its limiting norm.
Run the derivative estimate backward in the coordinate `s = 1/r`,
starting at a positive `s`, and only then take that end to zero. -/
theorem inverse_square_backward_bound (u du : ℝ → E) (C : ℝ) (hC : 0 ≤ C)
    (d : ∀ r, 2 < r → HasDerivAt u (du r) r)
    (bound : ∀ r, 2 < r → ‖du r‖ ≤ (C/r^2)*‖u r‖)
    {a : E} (limit : Tendsto u atTop (𝓝 a)) {R : ℝ} (hR : 2 < R) :
    ‖u R‖ ≤ ‖a‖*Real.exp (C/R) := by
  let Y := fun s : ℝ => u s⁻¹
  let DY := fun s : ℝ => (-(s^2)⁻¹ : ℝ) • du s⁻¹
  have r0 : 0 < R := by linarith
  have outside {s : ℝ} (hs : 0 < s) (h : s ≤ R⁻¹) : 2 < s⁻¹ := by
    have le := mul_le_mul_of_nonneg_left h r0.le
    rw [mul_inv_cancel₀ r0.ne'] at le
    exact hR.trans_le (by simpa only [one_div] using (le_div_iff₀ hs).2 le)
  have differentiate {s : ℝ} (hs : 0 < s) (h : s ≤ R⁻¹) : HasDerivAt Y (DY s) s := by
    simpa only [Y,DY,Function.comp_def] using (d _ (outside hs h)).scomp s (hasDerivAt_inv hs.ne')
  have scaled_bound {s : ℝ} (hs : 0 < s) (h : s ≤ R⁻¹) : ‖DY s‖ ≤ C*‖Y s‖ := by
    unfold DY
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity : 0 ≤ (s^2)⁻¹)]
    calc
      _ ≤ (s^2)⁻¹*((C/(s⁻¹)^2)*‖Y s‖) :=
        mul_le_mul_of_nonneg_left (bound _ (outside hs h)) (by positivity)
      _ = _ := by
        rw [inv_pow,div_inv_eq_mul]
        field_simp [hs.ne']
  have finite (b : ℝ) (hb : R ≤ b) : ‖u R‖ ≤ ‖u b‖*Real.exp (C/R) := by
    have b0 := r0.trans_le hb
    have order : b⁻¹ ≤ R⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le r0 hb
    have positive {s : ℝ} (hs : s ∈ Icc b⁻¹ R⁻¹) : 0 < s := (inv_pos.2 b0).trans_le hs.1
    have cont : ContinuousOn Y (Icc b⁻¹ R⁻¹) := fun _ h =>
      (differentiate (positive h) h.2).continuousAt.continuousWithinAt
    have step := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) cont
      (fun _ h => (differentiate (positive (Ico_subset_Icc_self h)) h.2.le).hasDerivWithinAt)
      (le_refl ‖Y b⁻¹‖)
      (fun _ h => by simpa only [add_zero] using scaled_bound (positive (Ico_subset_Icc_self h)) h.2.le)
      R⁻¹ ⟨order,le_rfl⟩
    rw [gronwallBound_ε0] at step
    simp only [Y,inv_inv] at step
    refine step.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr b0.le)) hC
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (limit.norm.mul_const (Real.exp (C/R)))
    ((eventually_ge_atTop R).mono finite)

/-- The forward bound retains the actual reciprocal-radius step. -/
theorem inverse_square_forward_bound (u du : ℝ → E) (C : ℝ)
    (d : ∀ r, 2 < r → HasDerivAt u (du r) r)
    (bound : ∀ r, 2 < r → ‖du r‖ ≤ (C/r^2)*‖u r‖)
    {R r : ℝ} (hR : 2 < R) (hr : R ≤ r) :
    ‖u r‖ ≤ ‖u R‖*Real.exp (C*(R⁻¹-r⁻¹)) := by
  let Y := fun t : ℝ => u (-t⁻¹)
  let DY := fun t : ℝ => ((t^2)⁻¹ : ℝ) • du (-t⁻¹)
  have R0 : 0 < R := by linarith
  have r0 : 0 < r := R0.trans_le hr
  have order : -R⁻¹ ≤ -r⁻¹ := by
    apply neg_le_neg
    simpa only [one_div] using one_div_le_one_div_of_le R0 hr
  have upper : -r⁻¹ < 0 := neg_lt_zero.2 (inv_pos.2 r0)
  have outside (t : ℝ) (ht : t ∈ Icc (-R⁻¹) (-r⁻¹)) : 2 < -t⁻¹ := by
    have nt : 0 < -t := neg_pos.2 (ht.2.trans_lt upper)
    have inv : -t ≤ R⁻¹ := by linarith [ht.1]
    have b : R*(-t) ≤ 1 := by
      simpa only [mul_inv_cancel₀ R0.ne'] using mul_le_mul_of_nonneg_left inv R0.le
    exact hR.trans_le (by simpa only [one_div,inv_neg] using (le_div_iff₀ nt).2 b)
  have localODE (t : ℝ) (ht : t ∈ Icc (-R⁻¹) (-r⁻¹)) : HasDerivAt Y (DY t) t := by
    have nz : t ≠ 0 := (ht.2.trans_lt upper).ne
    simpa only [Y,DY,neg_neg,Function.comp_def,Pi.neg_apply] using
      (d _ (outside t ht)).scomp t (hasDerivAt_inv nz).neg
  have localBound (t : ℝ) (ht : t ∈ Icc (-R⁻¹) (-r⁻¹)) : ‖DY t‖ ≤ C*‖Y t‖ := by
    have nz : t ≠ 0 := (ht.2.trans_lt upper).ne
    unfold DY
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (t^2)⁻¹)]
    calc
      _ ≤ (t^2)⁻¹*((C/(-t⁻¹)^2)*‖Y t‖) :=
        mul_le_mul_of_nonneg_left (bound _ (outside t ht)) (by positivity)
      _ = _ := by rw [neg_sq,inv_pow,div_inv_eq_mul]; field_simp [nz]
  have cont : ContinuousOn Y (Icc (-R⁻¹) (-r⁻¹)) := fun t ht =>
    (localODE t ht).continuousAt.continuousWithinAt
  have proof := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) cont
    (fun t ht => (localODE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (le_refl ‖Y (-R⁻¹)‖)
    (fun t ht => by simpa only [add_zero] using localBound t (Ico_subset_Icc_self ht))
    (-r⁻¹) ⟨order,le_rfl⟩
  rw [gronwallBound_ε0] at proof
  simp only [Y,inv_neg,inv_inv,neg_neg] at proof
  simpa only [sub_neg_eq_add,neg_add_eq_sub] using proof

#print axioms inverse_square_limit
#print axioms inverse_square_backward_bound
#print axioms inverse_square_forward_bound

end
end SchwarzschildLaurent.LinearWave
