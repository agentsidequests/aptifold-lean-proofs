
import AdmittedMixtureNumerators
import RationalLocalValues
import Mathlib.Tactic.Positivity

/-! Parameter denominators and the two distinct mixture ratios. -/
namespace SchwarzschildMixtures

open Polynomial SchwarzschildLaurent

noncomputable section

def gamma (ell : ℂ) : ℂ := (ell-1)*ell*(ell+1)*(ell+2)/12

def daughterGamma (ell : ℂ) : ℂ := gamma (2*ell)/2

def alternativeRatio (k ell : ℂ) : ℂ :=
  (daughterGamma ell + gamma ell)*(gamma ell-k)/((daughterGamma ell-gamma ell)*(gamma ell+k))

/-- The common denominator scalar after putting the three coefficients of
each explicit field and its source over the same respective denominators. -/
def fieldScalar (multiplier : ℕ) (second : Bool) (k ell : ℂ) : ℂ :=
  multiplier * ell*(ell-1)^2*(ell+2)^2*(2*ell+1)*(ell+1)^5*(2*ell-1)^5*
    k^2*(12*(k+gamma ell))^2*(6*(k-daughterGamma ell))*
    (if second then (7*ell-1)^2 else 1)

private theorem gamma_real (x : ℝ) : gamma (x : ℂ) = (↑((x-1)*x*(x+1)*(x+2)/12) : ℂ) := by
  unfold gamma
  push_cast
  rfl

private theorem gamma_gap (ell : ℂ) :
    daughterGamma ell - gamma ell = ell^2*(ell+1)*(7*ell-1)/12 := by
  unfold daughterGamma gamma
  ring

theorem gamma_positive (n : ℕ) (hn : 2 ≤ n) : 0 < (gamma (n : ℂ)).re := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h : (0 : ℝ) < (n : ℝ) := by linarith
  rw [← Complex.ofReal_natCast, gamma_real, Complex.ofReal_re]
  positivity

theorem gap_positive (n : ℕ) (hn : 2 ≤ n) :
    0 < (daughterGamma (n : ℂ) - gamma (n : ℂ)).re := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : (0 : ℝ) < 7*(n : ℝ)-1 := by linarith
  have h : (0 : ℝ) < (n : ℝ) := by linarith
  rw [gamma_gap, ← Complex.ofReal_natCast]
  push_cast
  norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im, pow_two]
  positivity

private theorem re_ne_zero {z : ℂ} (h : z.re ≠ 0) : z ≠ 0 := by
  intro hz
  exact h (by simp [hz])

theorem gamma_add_frequency (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    gamma (n : ℂ) + k ≠ 0 := by
  apply re_ne_zero
  simpa [Complex.add_re, ki] using (gamma_positive n hn).ne'

theorem frequency_sub_daughter (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    k - daughterGamma (n : ℂ) ≠ 0 := by
  have h := gap_positive n hn
  have g := gamma_positive n hn
  apply re_ne_zero
  simp only [Complex.sub_re, ki] at h ⊢
  linarith

theorem alternativeRatio_ne_one (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (ki : k.re = 0) :
    alternativeRatio k n ≠ 1 := by
  intro eq
  have hg := gamma_positive n hn
  have den := mul_ne_zero (re_ne_zero (gap_positive n hn).ne') (gamma_add_frequency n hn k ki)
  have h := (div_eq_iff den).mp eq
  simp only [one_mul] at h
  have num : (gamma (n : ℂ))^2 - daughterGamma (n : ℂ)*k = 0 := by
    linear_combination h/2
  have ig : (gamma (n : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast, gamma_real, Complex.ofReal_im]
  have iG : (daughterGamma (n : ℂ)).im = 0 := by
    have eq : (2 : ℂ) * (n : ℂ) = (↑(2*(n : ℝ)) : ℂ) := by push_cast; rfl
    rw [daughterGamma, eq, gamma_real]
    simp
  have hz := congrArg Complex.re num
  simp only [Complex.zero_re, Complex.sub_re, pow_two, Complex.mul_re, ig, iG, ki,
    mul_zero, zero_mul, sub_zero] at hz
  exact (mul_ne_zero hg.ne' hg.ne') hz

theorem fieldScalar_ne_zero (multiplier n : ℕ) (hm : 0 < multiplier) (hn : 2 ≤ n)
    (second : Bool) (k : ℂ) (hk : k ≠ 0) (ki : k.re = 0) :
    fieldScalar multiplier second k n ≠ 0 := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < (n : ℝ) := by linarith
  have hn₁ : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have hn₂ : (0 : ℝ) < 2*(n : ℝ)-1 := by linarith
  have hn₇ : (0 : ℝ) < 7*(n : ℝ)-1 := by linarith
  have cm : (multiplier : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have cn : (n : ℂ) ≠ 0 := by exact_mod_cast hn₀.ne'
  have csub : (n : ℂ)-1 ≠ 0 := by exact_mod_cast hn₁.ne'
  have cplus : (n : ℂ)+2 ≠ 0 := by exact_mod_cast (show (0 : ℝ) < (n : ℝ)+2 by positivity).ne'
  have cplus1 : (n : ℂ)+1 ≠ 0 := by exact_mod_cast (show (0 : ℝ) < (n : ℝ)+1 by positivity).ne'
  have ctwominus : 2*(n : ℂ)-1 ≠ 0 := by exact_mod_cast hn₂.ne'
  have ctwoplus : 2*(n : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < 2*(n : ℝ)+1 by positivity).ne'
  have cseven : 7*(n : ℂ)-1 ≠ 0 := by exact_mod_cast hn₇.ne'
  have cg : k + gamma (n : ℂ) ≠ 0 := by simpa [add_comm] using gamma_add_frequency n hn k ki
  have cG := frequency_sub_daughter n hn k ki
  cases second <;> simp [fieldScalar, cm, cn, csub, cplus, cplus1, ctwominus, ctwoplus,
    cseven, hk, cg, cG]

theorem parentPole_horizon_ne_zero (n : ℕ) (hn : 2 ≤ n) : (parentPole (n : ℂ)).eval 2 ≠ 0 := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : (0 : ℝ) < (n : ℝ)-1 := by linarith
  have h₂ : (0 : ℝ) < (n : ℝ)+2 := by linarith
  have h : (0 : ℝ) < 2*((n : ℝ)-1)*((n : ℝ)+2)+6 := by positivity
  apply re_ne_zero
  simpa [parentPole, Polynomial.eval_add, Polynomial.eval_mul, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, mul_assoc] using h.ne'

theorem daughterPole_horizon_ne_zero (n : ℕ) (hn : 2 ≤ n) : (daughterPole (n : ℂ)).eval 2 ≠ 0 := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : (0 : ℝ) < 2*(n : ℝ)-1 := by linarith
  have h₂ : (0 : ℝ) < (n : ℝ)+1 := by linarith
  have h : (0 : ℝ) < 2*(2*(n : ℝ)-1)*((n : ℝ)+1)+3 := by positivity
  apply re_ne_zero
  simpa [daughterPole, Polynomial.eval_add, Polynomial.eval_mul, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, mul_assoc] using h.ne'

private theorem poly_ne_of_eval {p : ℂ[X]} (h : p.eval 2 ≠ 0) : p ≠ 0 := by
  intro eq
  simp [eq] at h

theorem poles_ne_zero (n : ℕ) (hn : 2 ≤ n) : poles (n : ℂ) ≠ 0 :=
  mul_ne_zero (poly_ne_of_eval (parentPole_horizon_ne_zero n hn))
    (poly_ne_of_eval (daughterPole_horizon_ne_zero n hn))

theorem fieldDenominator_ne_zero (scalar : ℂ) (hs : scalar ≠ 0) (n : ℕ) (hn : 2 ≤ n) :
    fieldDenominator scalar n ≠ 0 := by
  have hshift : shiftedRadius ≠ 0 := by
    intro he
    have h := congrArg (Polynomial.eval (0 : ℂ)) he
    norm_num [shiftedRadius] at h
  simp [fieldDenominator, hs, hshift, poly_ne_of_eval (parentPole_horizon_ne_zero n hn),
    poly_ne_of_eval (daughterPole_horizon_ne_zero n hn)]

end
end SchwarzschildMixtures
