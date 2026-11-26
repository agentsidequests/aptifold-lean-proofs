import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Convergence of the normalized ingoing Regge–Wheeler series.
Here \(s=r-2\), and \(L=\ell(\ell+1)\) is the parent eigenvalue. -/
namespace SchwarzschildLaurent.Horizon

open FormalMultilinearSeries
open scoped NNReal ENNReal

noncomputable section

def horizonLeading (k : ℂ) (n : ℕ) : ℂ :=
  4*((n : ℂ)+1)*((n : ℂ)+1-4*k)

def horizonMiddle (k L : ℂ) (n : ℕ) : ℂ :=
  4*(n : ℂ)^2+(-(2+24*k))*(n : ℂ)+(6-2*L)

def horizonPrevious (k L : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ)^2+(-(3+12*k))*(n : ℂ)+(2+12*k-L)

def horizonOlder (k : ℂ) (n : ℕ) : ℂ :=
  (-2*k)*(n : ℂ)+4*k

/-- Store the current Taylor coefficient and its two predecessors.
Missing coefficients before the constant term are zero. -/
def horizonState (k L : ℂ) : ℕ → ℂ × ℂ × ℂ
  | 0 => (1,0,0)
  | n+1 =>
    let a := horizonState k L n
    (-(horizonMiddle k L n*a.1 + horizonPrevious k L n*a.2.1 + horizonOlder k n*a.2.2) /
        horizonLeading k n, a.1, a.2.1)

def horizonCoefficient (k L : ℂ) (n : ℕ) : ℂ := (horizonState k L n).1

private theorem leading_norm_lower_bound (k : ℂ) (ki : k.re = 0) (n : ℕ) :
    ((n : ℝ)+1)^2 ≤ ‖horizonLeading k n‖ := by
  have re : (((n : ℂ)+1)-4*k).re = (n : ℝ)+1 := by simp [Complex.mul_re, ki]
  have le : (n : ℝ)+1 ≤ ‖((n : ℂ)+1)-4*k‖ := re ▸ Complex.re_le_norm _
  have nm : ‖(n : ℂ)+1‖ = (n : ℝ)+1 := by
    simpa only [Nat.cast_succ] using Complex.norm_natCast (n+1)
  have nn : 0 ≤ (n : ℝ)+1 := by positivity
  rw [horizonLeading,norm_mul,norm_mul,nm]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left le nn, sq_nonneg ((n : ℝ)+1)]

theorem horizon_leading_ne_zero (k : ℂ) (ki : k.re = 0) (n : ℕ) :
    horizonLeading k n ≠ 0 := by
  have positive : 0 < ((n : ℝ)+1)^2 := by positivity
  exact norm_pos_iff.mp (positive.trans_le (leading_norm_lower_bound k ki n))

theorem horizon_coefficient_recurrence (k L : ℂ) (ki : k.re = 0) (n : ℕ) :
    horizonLeading k n*horizonCoefficient k L (n+1) +
      horizonMiddle k L n*(horizonState k L n).1 +
      horizonPrevious k L n*(horizonState k L n).2.1 +
      horizonOlder k n*(horizonState k L n).2.2 = 0 := by
  simp only [horizonCoefficient, horizonState]
  field_simp [horizon_leading_ne_zero k ki n]
  ring

private def normWeight (p q s : ℂ) : ℝ := ‖p‖+‖q‖+‖s‖

private theorem norm_quadratic_le (p q s : ℂ) (n : ℕ) :
    ‖p*(n : ℂ)^2+q*(n : ℂ)+s‖ ≤ normWeight p q s*((n : ℝ)+1)^2 := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (n : ℝ)^2 ≤ ((n : ℝ)+1)^2 := by nlinarith
  have h1 : (n : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n : ℝ)]
  have hu : 1 ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n : ℝ)]
  calc
    _ ≤ ‖p*(n : ℂ)^2‖+‖q*(n : ℂ)‖+‖s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖p‖*(n : ℝ)^2+‖q‖*(n : ℝ)+‖s‖*1 := by simp [norm_pow]
    _ ≤ ‖p‖*((n : ℝ)+1)^2+‖q‖*((n : ℝ)+1)^2+‖s‖*((n : ℝ)+1)^2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
    _ = _ := by unfold normWeight; ring

private def middleWeight (k L : ℂ) : ℝ := normWeight 4 (-(2+24*k)) (6-2*L)
private def previousWeight (k L : ℂ) : ℝ := normWeight 1 (-(3+12*k)) (2+12*k-L)
private def olderWeight (k : ℂ) : ℝ := normWeight 0 (-2*k) (4*k)

def horizonGrowth (k L : ℂ) : ℝ := 1+middleWeight k L+previousWeight k L+olderWeight k

private theorem one_le_growth (k L : ℂ) : 1 ≤ horizonGrowth k L := by
  unfold horizonGrowth middleWeight previousWeight olderWeight normWeight
  linarith [norm_nonneg (4 : ℂ), norm_nonneg (-(2+24*k)), norm_nonneg (6-2*L),
    norm_nonneg (1 : ℂ), norm_nonneg (-(3+12*k)), norm_nonneg (2+12*k-L),
    norm_nonneg (0 : ℂ), norm_nonneg (-2*k), norm_nonneg (4*k)]

private theorem recurrence_bound (k L : ℂ) (ki : k.re = 0) (n : ℕ)
    (a b c : ℂ) {M : ℝ} (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) :
    ‖-(horizonMiddle k L n*a+horizonPrevious k L n*b+horizonOlder k n*c)/horizonLeading k n‖
      ≤ horizonGrowth k L*M := by
  let d := ‖horizonLeading k n‖
  have dp : 0 < d := norm_pos_iff.mpr (horizon_leading_ne_zero k ki n)
  have lower := leading_norm_lower_bound k ki n
  have pa : ‖horizonMiddle k L n‖ ≤ middleWeight k L*d :=
    (norm_quadratic_le 4 (-(2+24*k)) (6-2*L) n).trans
      (mul_le_mul_of_nonneg_left lower (by unfold normWeight; positivity))
  have pb : ‖horizonPrevious k L n‖ ≤ previousWeight k L*d := by
    simpa only [horizonPrevious, previousWeight, one_mul] using
      (norm_quadratic_le 1 (-(3+12*k)) (2+12*k-L) n).trans
        (mul_le_mul_of_nonneg_left lower (by unfold normWeight; positivity))
  have pc : ‖horizonOlder k n‖ ≤ olderWeight k*d := by
    simpa only [horizonOlder, olderWeight, zero_mul, zero_add] using
      (norm_quadratic_le 0 (-2*k) (4*k) n).trans
        (mul_le_mul_of_nonneg_left lower (by unfold normWeight; positivity))
  rw [norm_div, norm_neg]
  apply (div_le_iff₀ dp).2
  calc
    _ ≤ ‖horizonMiddle k L n*a‖+‖horizonPrevious k L n*b‖+‖horizonOlder k n*c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ middleWeight k L*d*M+previousWeight k L*d*M+olderWeight k*d*M := by
      simp only [norm_mul]
      exact add_le_add (add_le_add (mul_le_mul pa ha (norm_nonneg _) (by linarith [norm_nonneg (horizonMiddle k L n)]))
        (mul_le_mul pb hb (norm_nonneg _) (by linarith [norm_nonneg (horizonPrevious k L n)])))
        (mul_le_mul pc hc (norm_nonneg _) (by linarith [norm_nonneg (horizonOlder k n)]))
    _ ≤ horizonGrowth k L*M*d := by
      unfold horizonGrowth
      nlinarith [mul_nonneg hM dp.le]

private theorem state_bound (k L : ℂ) (ki : k.re = 0) (n : ℕ) :
    let a := horizonState k L n
    ‖a.1‖ ≤ horizonGrowth k L ^ n ∧ ‖a.2.1‖ ≤ horizonGrowth k L ^ n ∧ ‖a.2.2‖ ≤ horizonGrowth k L ^ n := by
  induction n with
  | zero => simp [horizonState]
  | succ n ih =>
    have h := one_le_growth k L
    have hp : 0 ≤ horizonGrowth k L ^ n := pow_nonneg (zero_le_one.trans h) _
    have le : horizonGrowth k L ^ n ≤ horizonGrowth k L ^ (n+1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right hp h
    dsimp only [horizonState]
    refine ⟨?_,ih.1.trans le,ih.2.1.trans le⟩
    simpa only [pow_succ, mul_comm] using
      recurrence_bound k L ki n _ _ _ hp ih.1 ih.2.1 ih.2.2

/-- The actual convergent Taylor sum at \(s=0\). -/
def ingoingEnvelope (k L : ℂ) : ℂ → ℂ := ofScalarsSum (horizonCoefficient k L)

theorem horizon_coefficient_norm_bound (k L : ℂ) (ki : k.re = 0) (n : ℕ) :
    ‖horizonCoefficient k L n‖ ≤ horizonGrowth k L ^ n := (state_bound k L ki n).1

theorem horizon_growth_uniform (k : ℂ) (L : ℝ) (hk : ‖k‖ ≤ 1) (hL : 0 ≤ L) :
    horizonGrowth k (L:ℂ) ≤ 100+4*L := by
  have normL : ‖(L:ℂ)‖ = L := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
  have middleLinear : ‖2+24*k‖ ≤ 26 := by
    have bound := norm_add_le (2:ℂ) (24*k)
    simp only [norm_mul,Complex.norm_ofNat] at bound
    linarith
  have middleConstant : ‖6-2*(L:ℂ)‖ ≤ 6+2*L := by
    simpa only [norm_mul,Complex.norm_ofNat,normL] using norm_sub_le (6:ℂ) (2*(L:ℂ))
  have previousLinear : ‖3+12*k‖ ≤ 15 := by
    have bound := norm_add_le (3:ℂ) (12*k)
    simp only [norm_mul,Complex.norm_ofNat] at bound
    linarith
  have previousConstant : ‖2+12*k-(L:ℂ)‖ ≤ 14+L := by
    have subtract := norm_sub_le (2+12*k) (L:ℂ)
    have add := norm_add_le (2:ℂ) (12*k)
    simp only [norm_mul,Complex.norm_ofNat,normL] at add subtract
    linarith
  unfold horizonGrowth middleWeight previousWeight olderWeight normWeight
  simp only [norm_zero,norm_one,norm_neg,norm_mul,Complex.norm_ofNat]
  linarith

theorem ingoing_power_series_on_ball (k L : ℂ) (ki : k.re = 0)
    {r : ℝ≥0} (rpos : 0 < r) (majorant : horizonGrowth k L*(r:ℝ) ≤ 1) :
    HasFPowerSeriesOnBall (ingoingEnvelope k L) (ofScalars ℂ (horizonCoefficient k L)) 0 (r:ℝ≥0∞) := by
  have hr : 0 < (r:ℝ≥0∞) := by exact_mod_cast rpos
  have hg : 0 ≤ horizonGrowth k L := zero_le_one.trans (one_le_growth k L)
  let p := ofScalars ℂ (horizonCoefficient k L)
  have hrp : (r : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound 1
    intro n
    change ‖ofScalars ℂ (horizonCoefficient k L) n‖ * (r:ℝ)^n ≤ 1
    rw [ofScalars_norm]
    calc
      _ ≤ (horizonGrowth k L)^n * (r:ℝ)^n :=
        mul_le_mul_of_nonneg_right (horizon_coefficient_norm_bound k L ki n) (pow_nonneg r.coe_nonneg _)
      _ = (horizonGrowth k L*(r:ℝ))^n := (mul_pow _ _ _).symm
      _ ≤ (1:ℝ)^n := pow_le_pow_left₀ (mul_nonneg hg r.coe_nonneg) majorant n
      _ = 1 := one_pow n
  exact (p.hasFPowerSeriesOnBall (hr.trans_le hrp)).mono hr hrp

theorem ingoing_has_power_series (k L : ℂ) (ki : k.re = 0) :
    HasFPowerSeriesAt (ingoingEnvelope k L) (ofScalars ℂ (horizonCoefficient k L)) 0 := by
  have hg : 0 < horizonGrowth k L := zero_lt_one.trans_le (one_le_growth k L)
  let r : ℝ≥0 := ⟨(horizonGrowth k L)⁻¹,inv_nonneg.mpr hg.le⟩
  have rpos : 0 < r := inv_pos.mpr hg
  have product : horizonGrowth k L*(r:ℝ) ≤ 1 := (mul_inv_cancel₀ hg.ne').le
  exact (ingoing_power_series_on_ball k L ki rpos product).hasFPowerSeriesAt

@[simp] theorem ingoing_envelope_zero (k L : ℂ) : ingoingEnvelope k L 0 = 1 := by
  simp [ingoingEnvelope, ofScalarsSum_zero, horizonCoefficient, horizonState]

#print axioms horizon_coefficient_recurrence
#print axioms horizon_coefficient_norm_bound
#print axioms horizon_growth_uniform
#print axioms ingoing_power_series_on_ball
#print axioms ingoing_has_power_series
#print axioms ingoing_envelope_zero

end
end SchwarzschildLaurent.Horizon
