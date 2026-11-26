import HorizonFrobeniusEquation
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform Taylor tails at a real seed inside the convergent horizon
series. The estimates also apply to the derivative series. -/
namespace SchwarzschildLaurent.Horizon

open Filter FormalMultilinearSeries
open scoped Topology NNReal ENNReal

noncomputable section

private theorem norm_le_geometric {f : ℕ → ℂ} {v : ℂ} (sum : HasSum f v)
    {B q : ℝ} (q0 : 0 ≤ q) (q1 : q < 1) (bound : ∀ n, ‖f n‖ ≤ B*q^n) :
    ‖v‖ ≤ B/(1-q) := by
  have geom := (hasSum_geometric_of_lt_one q0 q1).mul_left B
  have le : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, f i‖ ≤ ∑ i ∈ Finset.range n, B*q^i := by
    intro n
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => bound i)
  simpa only [div_eq_mul_inv] using
    le_of_tendsto_of_tendsto sum.tendsto_sum_nat.norm geom.tendsto_sum_nat (Eventually.of_forall le)

private theorem index_le_double_power (m : ℕ) : (m:ℝ)+2 ≤ (2:ℝ)^(m+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.cast_succ,show m.succ+1 = (m+1)+1 from rfl,pow_succ]
    linarith [show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m]

theorem uniform_taylor_seed_bounds (a : ℕ → ℂ) (value jet : ℂ) (C d : ℝ)
    (C0 : 0 < C) (d0 : 0 < d) (small : C*d ≤ 1/4)
    (coeff : ∀ n, ‖a n‖ ≤ C^n)
    (series : HasSum (fun n : ℕ => a n*(d:ℂ)^n) value)
    (derivSeries : HasSum (fun n : ℕ => ((n:ℂ)+1)*a (n+1)*(d:ℂ)^n) jet) :
    ‖value-a 0‖ ≤ 2*C*d ∧ ‖jet-a 1‖ ≤ 4*C^2*d := by
  let q := C*d
  have q0 : 0 ≤ q := mul_nonneg C0.le d0.le
  have q1 : q < 1 := by change C*d < 1; linarith
  have q2 : 2*q < 1 := by change 2*(C*d) < 1; linarith
  have nd : ‖(d:ℂ)‖ = d := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos d0]
  have v := (hasSum_nat_add_iff' 1).mpr series
  simp only [Finset.sum_range_one,pow_zero,mul_one] at v
  have e := (hasSum_nat_add_iff' 1).mpr derivSeries
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_add,one_mul,pow_zero,mul_one] at e
  have vb : ‖value-a 0‖ ≤ q/(1-q) := by
    apply norm_le_geometric v q0 q1
    intro n
    simp only [norm_mul,norm_pow,nd]
    calc
      _ ≤ C^(n+1)*d^(n+1) := mul_le_mul_of_nonneg_right (coeff _) (pow_nonneg d0.le _)
      _ = q*q^n := by rw [← mul_pow,pow_succ']
  have eb : ‖jet-a 1‖ ≤ (C*(2*q))/(1-2*q) := by
    apply norm_le_geometric e (by positivity) q2
    intro n
    have normIndex : ‖((n+1:ℕ):ℂ)+1‖ = (n:ℝ)+2 := by
      simp only [Nat.cast_add,Nat.cast_one,← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1+1)]
      ring
    simp only [norm_mul,norm_pow,nd,normIndex]
    calc
      _ ≤ ((n:ℝ)+2)*C^((n+1)+1)*d^(n+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coeff _) (by positivity)) (pow_nonneg d0.le _)
      _ = C*(((n:ℝ)+2)*(C^(n+1)*d^(n+1))) := by rw [pow_succ C]; ring
      _ = C*(((n:ℝ)+2)*q^(n+1)) := by rw [← mul_pow]
      _ ≤ C*((2:ℝ)^(n+1)*q^(n+1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (index_le_double_power n) (pow_nonneg q0 _)) C0.le
      _ = (C*(2*q))*(2*q)^n := by rw [← mul_pow,pow_succ']; ring
  constructor
  · apply vb.trans
    rw [show 2*C*d = 2*q by dsimp only [q]; ring]
    apply (div_le_iff₀ (sub_pos.mpr q1)).2
    have b : 1 ≤ 2*(1-q) := by change (1:ℝ) ≤ 2*(1-C*d); linarith
    linarith [mul_le_mul_of_nonneg_left b q0]
  · apply eb.trans
    have b : (C*(2*q))/(1-2*q) ≤ 4*C*q := by
      apply (div_le_iff₀ (sub_pos.mpr q2)).2
      have m : 1 ≤ 2*(1-2*q) := by change (1:ℝ) ≤ 2*(1-2*(C*d)); linarith
      have scale : 0 ≤ C*(2*q) := mul_nonneg C0.le (mul_nonneg (by norm_num) q0)
      calc
        C*(2*q) = C*(2*q)*1 := by ring
        _ ≤ C*(2*q)*(2*(1-2*q)) := mul_le_mul_of_nonneg_left m scale
        _ = 4*C*q*(1-2*q) := by ring
    calc
      _ ≤ 4*C*q := b
      _ = _ := by dsimp only [q]; ring

theorem scalar_derivative_sum_on_ball {f : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 R)
    {z : ℂ} (inside : z ∈ Metric.eball 0 R) :
    HasSum (fun n : ℕ => ((n:ℂ)+1)*a (n+1)*z^n) (deriv f z) := by
  let eval := ContinuousLinearMap.apply ℂ ℂ (1:ℂ)
  let p := eval.compFormalMultilinearSeries (ofScalars ℂ a).derivSeries
  have compiled := (eval.comp_hasFPowerSeriesOnBall h.fderiv).hasSum_sub inside
  have coeff (n : ℕ) : p.coeff n = ((n:ℂ)+1)*a (n+1) := by
    change (ofScalars ℂ a).derivSeries.coeff n (1:ℂ) = _
    rw [derivSeries_coeff_one,coeff_ofScalars]
    simp [nsmul_eq_mul,Nat.cast_succ]
  have eq : (fun n => p n (fun _ => z-0)) = (fun n : ℕ => ((n:ℂ)+1)*a (n+1)*z^n) := by
    funext n
    rw [sub_zero,apply_eq_pow_smul_coeff,coeff,smul_eq_mul,mul_comm]
  change HasSum (fun n => p n (fun _ => z-0)) ((⇑eval ∘ fderiv ℂ f) z) at compiled
  rw [eq] at compiled
  simpa only [Function.comp_apply,eval,ContinuousLinearMap.apply_apply,fderiv_apply_one_eq_deriv] using compiled

/-- The horizon envelope and its derivative, evaluated inside a common
geometric radius, have the stated uniform first-term errors. -/
theorem ingoing_seed_tails (k : ℂ) (L : ℝ) (ki : k.re = 0) (knorm : ‖k‖ ≤ 1)
    (Lnonnegative : 0 ≤ L) {d : ℝ} (dpos : 0 < d) (small : (100+4*L)*d ≤ 1/4) :
    ‖ingoingEnvelope k (L:ℂ) (d:ℂ)-1‖ ≤ 2*(100+4*L)*d ∧
      ‖deriv (ingoingEnvelope k (L:ℂ)) (d:ℂ)-((L:ℂ)-3)/(2*(1-4*k))‖ ≤ 4*(100+4*L)^2*d := by
  let C : ℝ := 100+4*L
  have Cpos : 0 < C := by unfold C; linarith
  let radius : ℝ≥0 := ⟨C⁻¹,inv_nonneg.mpr Cpos.le⟩
  have rp : 0 < radius := inv_pos.mpr Cpos
  have growth : horizonGrowth k (L:ℂ) ≤ C := horizon_growth_uniform k L knorm Lnonnegative
  have product : horizonGrowth k (L:ℂ)*(radius:ℝ) ≤ 1 := by
    change horizonGrowth k (L:ℂ)*C⁻¹ ≤ 1
    rw [← mul_inv_cancel₀ Cpos.ne']
    exact mul_le_mul_of_nonneg_right growth (inv_nonneg.mpr Cpos.le)
  have onBall := ingoing_power_series_on_ball k (L:ℂ) ki rp product
  have inside : (d:ℂ) ∈ Metric.eball (0:ℂ) (radius:ℝ≥0∞) := by
    rw [Metric.eball_coe,Metric.mem_ball,dist_eq_norm,sub_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos dpos]
    change d < C⁻¹
    rw [← one_div]
    apply (lt_div_iff₀ Cpos).2
    dsimp only [C]
    linarith [small]
  have value := onBall.hasSum_sub inside
  simp only [sub_zero,ofScalars_apply_eq,smul_eq_mul] at value
  have derivative := scalar_derivative_sum_on_ball onBall inside
  have growth0 : 0 ≤ horizonGrowth k (L:ℂ) := by
    have one := horizon_coefficient_norm_bound k (L:ℂ) ki 1
    rw [pow_one] at one
    exact (norm_nonneg _).trans one
  have cBound (n : ℕ) : ‖horizonCoefficient k (L:ℂ) n‖ ≤ C^n :=
    (horizon_coefficient_norm_bound k (L:ℂ) ki n).trans (pow_le_pow_left₀ growth0 growth n)
  have a₁ := ingoing_envelope_derivative k (L:ℂ) ki
  rw [(ingoing_has_power_series k (L:ℂ) ki).deriv] at a₁
  change (ofScalars ℂ (horizonCoefficient k (L:ℂ))).coeff 1 = _ at a₁
  rw [coeff_ofScalars] at a₁
  have bounds := uniform_taylor_seed_bounds (horizonCoefficient k (L:ℂ)) _ _ C d Cpos dpos
    small cBound value derivative
  rw [show horizonCoefficient k (L:ℂ) 0 = 1 from rfl,a₁] at bounds
  exact bounds

#print axioms uniform_taylor_seed_bounds
#print axioms scalar_derivative_sum_on_ball
#print axioms ingoing_seed_tails

end
end SchwarzschildLaurent.Horizon
