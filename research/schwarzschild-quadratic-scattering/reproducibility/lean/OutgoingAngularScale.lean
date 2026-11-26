import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The master-to-strain and maximal-m harmonic factors in the
normalization used by the paper. -/
namespace SchwarzschildLaurent.Outgoing

noncomputable section

def masterFactor (j : ℕ) : ℝ :=
  Real.sqrt (((j+2).factorial : ℝ)/((j-2).factorial : ℝ))/2

def harmonicFactor (j : ℕ) : ℝ :=
  Real.sqrt (((2*j+1).factorial : ℝ)/(4*Real.pi*2^(2*j)*(j.factorial : ℝ)^2))

def angularScale (n : ℕ) : ℝ :=
  masterFactor (2*n)*harmonicFactor n^2/(harmonicFactor (2*n)*masterFactor n^2)

def angularCubic (x : ℝ) : ℝ := 20*x^3+35*x^2+x-8

def angularQuotient (n : ℕ) : ℝ :=
  let x : ℝ := n
  angularCubic x*x^2*(x-1)^2*(x+1)*(x+2)/(288*(2*x-1))

def printedScale (n : ℕ) : ℝ :=
  ((2*n+1).factorial : ℝ)*angularCubic n/
      (144*((n-1).factorial : ℝ)*((n-2).factorial : ℝ)) *
    Real.sqrt (((2*n+2).factorial : ℝ)*((2*n-2).factorial : ℝ)/
      (Real.pi*((4*n+1).factorial : ℝ)))

theorem masterFactor_positive (j : ℕ) : 0 < masterFactor j := by
  unfold masterFactor
  positivity

private theorem master_square (j : ℕ) :
    masterFactor j^2 = ((j+2).factorial : ℝ)/(4*((j-2).factorial : ℝ)) := by
  unfold masterFactor
  rw [div_pow, Real.sq_sqrt (by positivity)]
  ring

private theorem harmonic_square (j : ℕ) :
    harmonicFactor j^2 = ((2*j+1).factorial : ℝ)/(4*Real.pi*2^(2*j)*(j.factorial : ℝ)^2) := by
  unfold harmonicFactor
  exact Real.sq_sqrt (by positivity)

private theorem factorial_step {n m : ℕ} (h : n = m+1) :
    (n.factorial : ℝ) = n*(m.factorial : ℝ) := by
  subst n
  rw [Nat.factorial_succ, Nat.cast_mul]

private theorem parent_master_square (n : ℕ) (hn : 2 ≤ n) :
    masterFactor n^2 = ((n : ℝ)-1)*n*(n+1)*(n+2)/4 := by
  have a := factorial_step (n := n+2) (m := n+1) rfl
  have b := factorial_step (n := n+1) (m := n) rfl
  have c := factorial_step (n := n) (m := n-1) (by omega)
  have d := factorial_step (n := n-1) (m := n-2) (by omega)
  have f : ((n-2).factorial : ℝ) ≠ 0 := by positivity
  rw [master_square,a,b,c,d]
  simp only [Nat.cast_add,Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one,Nat.cast_ofNat]
  field_simp [f]

private theorem reduced_scale (q a w v c t z Y : ℝ)
    (hq : 0 ≤ q) (ha : 0 < a) (hv : 0 < v) (hc : 0 < c) (ht : 0 < t)
    (hz : 0 < z) (hY : 0 < Y) :
    (Real.sqrt (q/a)/2)*(w/(4*Real.pi*Y*c^2))/(Real.sqrt (z/(4*Real.pi*Y^2*v^2))*(t/4)) =
      w*v/(c^2*t)*Real.sqrt (q/(a*Real.pi*z)) := by
  have piPos := Real.pi_pos
  have rootDen : Real.sqrt (4*Real.pi*Y^2*v^2) = 2*Real.sqrt Real.pi*Y*v := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4*Real.pi*Y^2),
      Real.sqrt_mul (by positivity : 0 ≤ 4*Real.pi),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      Real.sqrt_sq hY.le,Real.sqrt_sq hv.le]
    have four : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num,Real.sqrt_sq (by norm_num)]
    rw [four]
  have rebracket : q/(a*Real.pi*z) = (q/a)/(Real.pi*z) := by
    field_simp [ha.ne',piPos.ne',hz.ne']
  have Sπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 piPos
  have Sz : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  rw [Real.sqrt_div hz.le,rootDen,rebracket,Real.sqrt_div (div_nonneg hq ha.le) (Real.pi*z),
    Real.sqrt_mul piPos.le]
  field_simp [ha.ne',hv.ne',hc.ne',ht.ne',hz.ne',hY.ne',piPos.ne',Sπ.ne',Sz.ne']
  ring_nf
  rw [Real.sq_sqrt piPos.le]

private theorem angular_scale_reduced (n : ℕ) (hn : 2 ≤ n) :
    angularScale n =
      ((2*n+1).factorial : ℝ)*((2*n).factorial : ℝ) /
        ((n.factorial : ℝ)^2*(((n : ℝ)-1)*n*(n+1)*(n+2))) *
      Real.sqrt (((2*n+2).factorial : ℝ)/(((2*n-2).factorial : ℝ)*Real.pi*((4*n+1).factorial : ℝ))) := by
  have power : (2:ℝ)^(2*(2*n)) = ((2:ℝ)^(2*n))^2 := by
    rw [← pow_mul]
    congr 1
    omega
  have angleIndex : 2*(2*n)+1 = 4*n+1 := by omega
  have nx : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have nx₁ : 0 < (n : ℝ)-1 := by linarith
  unfold angularScale
  rw [harmonic_square,parent_master_square n hn]
  unfold masterFactor harmonicFactor
  rw [power,angleIndex]
  exact reduced_scale _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)

private theorem move_factorial_under_root (q a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    a*Real.sqrt (q/(a*Real.pi*z)) = Real.sqrt (q*a/(Real.pi*z)) := by
  calc
    _ = Real.sqrt (a^2)*Real.sqrt (q/(a*Real.pi*z)) := by rw [Real.sqrt_sq ha.le]
    _ = _ := by
      rw [← Real.sqrt_mul (sq_nonneg a)]
      congr 1
      field_simp [ha.ne', Real.pi_pos.ne',hz.ne']

theorem angular_scale_matches_printed_factor (n : ℕ) (hn : 2 ≤ n) :
    angularScale n * angularQuotient n = printedScale n := by
  have even₁ := factorial_step (n := 2*n) (m := 2*n-1) (by omega)
  have even₂ := factorial_step (n := 2*n-1) (m := 2*n-2) (by omega)
  have parent₁ := factorial_step (n := n) (m := n-1) (by omega)
  have parent₂ := factorial_step (n := n-1) (m := n-2) (by omega)
  have rr := move_factorial_under_root ((2*n+2).factorial : ℝ) ((2*n-2).factorial : ℝ)
    ((4*n+1).factorial : ℝ) (by positivity) (by positivity)
  have nx : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have f₁ : ((n-1).factorial : ℝ) ≠ 0 := by positivity
  have f₂ : ((n-2).factorial : ℝ) ≠ 0 := by positivity
  have nz : (n : ℝ) ≠ 0 := by linarith
  have nz₁ : (n : ℝ)-1 ≠ 0 := by linarith
  have nz₂ : 2*(n : ℝ)-1 ≠ 0 := by linarith
  have plus₁ : (n : ℝ)+1 ≠ 0 := by linarith
  have plus₂ : (n : ℝ)+2 ≠ 0 := by linarith
  rw [angular_scale_reduced n hn]
  unfold angularQuotient printedScale
  rw [← rr,even₁,even₂,parent₁,parent₂]
  simp only [Nat.cast_sub (show 1 ≤ 2*n by omega),Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  field_simp [nz,nz₁,nz₂,plus₁,plus₂,f₁,f₂] <;> ring

#print axioms masterFactor_positive
#print axioms angular_scale_matches_printed_factor

end
end SchwarzschildLaurent.Outgoing
