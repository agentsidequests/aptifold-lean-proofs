import SoftCubicTransfer
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The harmonic-sum deficit determines the leading real threshold
coefficient. Two telescoping bounds suffice for every angular label. -/
namespace SchwarzschildMixtures.Strain

open Finset Filter
open SchwarzschildLaurent.Outgoing (printedScale)
open scoped Topology

noncomputable section

def harmonicIncrement (n m : ℕ) : ℝ :=
  ∑ j ∈ range m, 1/((n:ℝ)+(j:ℝ)+1)

def harmonicDeficit (n m : ℕ) : ℝ :=
  Real.log ((n:ℝ)+m)-Real.log (n:ℝ)-harmonicIncrement n m

private theorem log_deficit_bounds {x : ℝ} (hx : 0 ≤ x) (x1 : x < 1) :
    x^2/2 ≤ -Real.log (1-x)-x ∧ -Real.log (1-x)-x ≤ x^2/(2*(1-x)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg hx])
  have hTail : HasSum (fun j : ℕ => x^(j+1+1)/((j:ℝ)+1+1)) (-Real.log (1-x)-x) := by
    simpa only [Finset.sum_range_one,Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add,
      Nat.zero_add,pow_one,div_one] using (hasSum_nat_add_iff' 1).mpr h
  have geo := (hasSum_geometric_of_lt_one hx x1).mul_left (x^2/2)
  have lo := hTail.summable.le_tsum 0 (fun j _ => by positivity)
  rw [hTail.tsum_eq] at lo
  have hi := hTail.summable.tsum_le_tsum (fun j => show _ ≤ (x^2/2)*x^j from by
    calc
      _ ≤ x^(j+1+1)/2 :=
        div_le_div_of_nonneg_left (pow_nonneg hx _) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) j])
      _ = _ := by rw [show j+1+1 = j+2 by omega,pow_add]; ring) geo.summable
  rw [hTail.tsum_eq,geo.tsum_eq] at hi
  norm_num at lo
  refine ⟨lo,?_⟩
  rwa [div_mul_eq_div_div,div_eq_mul_inv (x^2/2)]

private theorem harmonic_deficit_step (n m : ℕ) (hn : 0 < n) :
    harmonicDeficit n (m+1)-harmonicDeficit n m =
      -Real.log (1-1/((n:ℝ)+m+1))-1/((n:ℝ)+m+1) := by
  let a : ℝ := (n:ℝ)+m
  have n0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have a0 : 0 < a := by dsimp [a]; positivity
  have a1 : 0 < a+1 := by positivity
  have eq : 1-1/(a+1) = a/(a+1) := by field_simp [a1.ne']; ring
  unfold harmonicDeficit harmonicIncrement
  rw [sum_range_succ]
  push_cast
  rw [← add_assoc]
  change (Real.log (a+1)-Real.log (n:ℝ)-(_+1/(a+1)))-
    (Real.log a-Real.log (n:ℝ)-_) = _
  rw [eq,Real.log_div a0.ne' a1.ne']
  ring

theorem harmonic_deficit_bounds (n m : ℕ) (hn : 0 < n) :
    (1/((n:ℝ)+1)-1/((n:ℝ)+m+1))/2 ≤ harmonicDeficit n m ∧
      harmonicDeficit n m ≤ (1/(n:ℝ)-1/((n:ℝ)+m))/2 := by
  have n0 : 0 < (n:ℝ) := by exact_mod_cast hn
  induction m with
  | zero => simp [harmonicDeficit,harmonicIncrement]
  | succ m ih =>
    let a : ℝ := (n:ℝ)+m
    have a0 : 0 < a := by dsimp [a]; positivity
    have a1 : 0 < a+1 := by positivity
    have a2 : 0 < a+2 := by positivity
    have x0 : 0 ≤ 1/(a+1) := by positivity
    have x1 : 1/(a+1) < 1 := (div_lt_iff₀ a1).2 (by linarith)
    obtain ⟨incLow,incHigh⟩ := log_deficit_bounds x0 x1
    rw [← harmonic_deficit_step n m hn] at incLow incHigh
    have low : (1/(a+1)-1/(a+2))/2 ≤ (1/(a+1))^2/2 := by
      have rel : (a+1)^2 ≤ (a+1)*(a+2) := by nlinarith
      calc
        _ = 1/(2*((a+1)*(a+2))) := by field_simp [a1.ne',a2.ne']; ring
        _ ≤ 1/(2*(a+1)^2) := one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left rel (by norm_num))
        _ = _ := by field_simp (disch := first | positivity | linarith)
    have high : (1/(a+1))^2/(2*(1-1/(a+1))) = (1/a-1/(a+1))/2 := by
      have nz : 1-1/(a+1) ≠ 0 := sub_ne_zero.mpr x1.ne'
      field_simp [a0.ne',a1.ne',nz]
      ring
    rw [high] at incHigh
    have substep := low.trans incLow
    have step : (n:ℝ)+↑(m+1) = a+1 := by push_cast; ring
    rw [step,show a+1+1 = a+2 by ring]
    constructor
    · linarith [ih.1]
    · linarith [ih.2]

def secondPhaseGap (n : ℕ) : ℝ :=
  -harmonicDeficit n n+2/((n:ℝ)*(n+1))-2/(2*(n:ℝ)*(2*n+1))

theorem harmonic_deficit_at_double (n : ℕ) (hn : 0 < n) :
    harmonicDeficit n n = Real.log 2-harmonicIncrement n n := by
  have n0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold harmonicDeficit
  rw [← two_mul,Real.log_mul (by norm_num) n0]
  ring

theorem second_phase_gap_negative_at_large_label (n : ℕ) (hn : 7 ≤ n) :
    secondPhaseGap n < 0 := by
  let l : ℝ := n
  have l7 : 7 ≤ l := by change (7:ℝ) ≤ (n:ℝ); exact_mod_cast hn
  have l0 : 0 < l := by linarith
  have l1 : 0 < l+1 := by positivity
  have l2 : 0 < 2*l+1 := by positivity
  have num : 0 < l^2/2-3*l-1 := by nlinarith [sq_nonneg (l-7)]
  have raw := (harmonic_deficit_bounds n n (by omega)).1
  have final : -secondPhaseGap n ≥ (l^2/2-3*l-1)/(l*(l+1)*(2*l+1)) := by
    unfold secondPhaseGap
    have eq :
        (1/(l+1)-1/(l+l+1))/2-2/(l*(l+1))+2/(2*l*(2*l+1)) =
          (l^2/2-3*l-1)/(l*(l+1)*(2*l+1)) := by
      rw [← two_mul l]
      field_simp
      ring
    change (1/(l+1)-1/(l+l+1))/2 ≤ harmonicDeficit n n at raw
    rw [← eq]
    change _ ≤ -(-harmonicDeficit n n+2/(l*(l+1))-2/(2*l*(2*l+1)))
    linarith
  exact neg_pos.mp ((div_pos num (by positivity)).trans_le final)

theorem second_threshold_factor_positive (n : ℕ) (hn : 2 ≤ n) (a b : ℝ)
    (phase : a-b = 8*secondPhaseGap n+4/parentRate n) :
    0 < secondThresholdFactor (parentRate n) (daughterRate n) a b := by
  let g := parentRate n
  let G := daughterRate n
  have g0 : 0 < g := parent_rate_positive n hn
  have gG : g < G := daughter_rate_gt_parent n hn
  have G0 := g0.trans gG
  have reduce : secondThresholdFactor g G a b = (1/g-1/G)^2-8*secondPhaseGap n/G := by
    unfold secondThresholdFactor
    change a-b = 8*secondPhaseGap n+4/g at phase
    rw [phase]
    field_simp [g0.ne',G0.ne']
    ring
  change 0 < secondThresholdFactor g G a b
  rw [reduce]
  by_cases h : 7 ≤ n
  · exact sub_pos.mpr ((div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num)
      (second_phase_gap_negative_at_large_label n h)) G0).trans_le (sq_nonneg _))
  · have pos : 0 < n := by omega
    rw [secondPhaseGap,harmonic_deficit_at_double n pos]
    dsimp only [g,G]
    have hi : n ≤ 6 := by omega
    interval_cases n <;>
      norm_num [parentRate,daughterRate,secondPhaseGap,harmonicIncrement,Finset.sum_range_succ] <;>
      linarith [Real.log_two_gt_d9]

/-- The published second-order linear phase inputs imply a single sign
change in the first correction to the magnitude of the second strain. -/
theorem second_strain_slope_sign (n : ℕ) (hn : 2 ≤ n)
    (rp rd F : ℝ → ℂ) (a b : ℝ) (unit : ∀ w, ‖F w‖ = 1)
    (phase : a-b = 8*secondPhaseGap n+4/parentRate n)
    (hp : Tendsto (quadraticQuotient (fun w => (rp w)^2/F w) 1 (a:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (((a^2/2:ℝ):ℂ)+((8*Real.pi*spinTwoAngularCorrection n:ℝ):ℂ)*Complex.I)))
    (hd : Tendsto (quadraticQuotient (fun w => -rd w/F w) 1 (b:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (((b^2/2:ℝ):ℂ)+((16*Real.pi*spinTwoAngularCorrection (2*n):ℝ):ℂ)*Complex.I))) :
    let G := daughterRate n
    let η := printedScale n/(4*G)
    let v := secondThresholdFactor (parentRate n) G a b
    ∃ σ : ℝ, Tendsto (fun w =>
        (‖printedResponse true (frequencyParameter w) n (rp w) (rd w)‖/(η*v*w^2)-1)/w)
        (𝓝[>] (0:ℝ)) (𝓝 σ) ∧
      (n ≤ 4 → σ < 0) ∧ (5 ≤ n → 0 < σ) := by
  let G := daughterRate n
  let v := secondThresholdFactor (parentRate n) G a b
  have vp : 0 < v := second_threshold_factor_positive n hn a b phase
  have Gp : 0 < G := (parent_rate_positive n hn).trans (daughter_rate_gt_parent n hn)
  have scale : 0 < 8*Real.pi/(G*v) := by positivity
  refine ⟨8*Real.pi/(G*v)*angularPhaseDifference n,
    second_magnitude_slope_from_linear_phases n hn rp rd F a b unit hp hd vp,?_⟩
  constructor
  · intro h
    exact mul_neg_of_pos_of_neg scale (cubic_phase_shift_negative n hn h)
  · intro h
    exact mul_pos scale (cubic_phase_shift_positive n (by exact_mod_cast h))

#print axioms harmonic_deficit_bounds
#print axioms harmonic_deficit_at_double
#print axioms second_phase_gap_negative_at_large_label
#print axioms second_threshold_factor_positive
#print axioms second_strain_slope_sign

end
end SchwarzschildMixtures.Strain
