import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Leading coefficient calculations for Appendix A of the Schwarzschild manuscript.
Rows use the basis (J², JZ, Z²), except at the horizon and infinity where
(J², J DJ, (DJ)²) is used. At the horizon the two bases differ by units.
-/

namespace SchwarzschildLaurent

abbrev Row (K : Type*) := K × K × K

def scale [Mul K] (s : K) (u : Row K) : Row K :=
  (s * u.1, s * u.2.1, s * u.2.2)

def plus [Add K] (u v : Row K) : Row K :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

def minus [Sub K] (u v : Row K) : Row K :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

def jet [CommRing K] (a b c : K) (u : Row K) : Row K :=
  (a * u.2.1, 2 * c * u.1 + b * u.2.1 + 2 * a * u.2.2,
    c * u.2.1 + 2 * b * u.2.2)

private theorem row_zero [Zero K] {u : Row K}
    (hp : u.1 = 0) (hq : u.2.1 = 0) (hs : u.2.2 = 0) : u = 0 :=
  Prod.ext hp (Prod.ext hq hs)

theorem scale_eq_zero [Field K] {z : K} {u : Row K}
    (hz : z ≠ 0) (h : scale z u = 0) : u = 0 := by
  apply row_zero
  · exact (mul_eq_zero.mp (congrArg Prod.fst h)).resolve_left hz
  · exact (mul_eq_zero.mp (congrArg (fun v => v.2.1) h)).resolve_left hz
  · exact (mul_eq_zero.mp (congrArg (fun v => v.2.2) h)).resolve_left hz

private theorem scale_zero [CommRing K] (z : K) : scale z (0 : Row K) = 0 := by
  apply row_zero <;> simp [scale]

private theorem row_zero_minus [CommRing K] (u : Row K) : minus 0 u = -u := by
  apply Prod.ext
  · simp [minus]
  · apply Prod.ext <;> simp [minus]

/-- The leading ordinary-point coefficient at order m+2. -/
def ordinaryIndicial (f : ℂ) (m : ℕ) (u : Row ℂ) : Row ℂ :=
  scale ((m : ℂ) * ((m : ℂ) + 1) * f ^ 2) u

theorem ordinary_pole_forces_leading_term (m : ℕ) (hm : 0 < m)
    (f : ℂ) (hf : f ≠ 0) {u : Row ℂ} (hu : u ≠ 0) :
    ordinaryIndicial f m u ≠ 0 := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
  exact fun h => hu (scale_eq_zero (mul_ne_zero (mul_ne_zero hm0 hm1) (pow_ne_zero _ hf)) h)

private def mode (t : ℂ) (u : Row ℂ) : ℂ :=
  u.1 + t * u.2.1 + t ^ 2 * u.2.2

private def centralMode (t : ℂ) (u : Row ℂ) : ℂ :=
  u.1 - t ^ 2 * u.2.2

private theorem modes_separate (t : ℂ) (ht : t ≠ 0) (u : Row ℂ)
    (hp : mode t u = 0) (hm : mode (-t) u = 0) (hc : centralMode t u = 0) :
    u = 0 := by
  have u1 : (4 : ℂ) * u.1 = 0 := by
    dsimp [mode, centralMode] at *
    linear_combination hp + hm + 2 * hc
  have u2 : (2 * t) * u.2.1 = 0 := by
    dsimp [mode] at *
    linear_combination hp - hm
  have u3 : (4 * t ^ 2) * u.2.2 = 0 := by
    dsimp [mode, centralMode] at *
    linear_combination hp + hm - 2 * hc
  exact row_zero ((mul_eq_zero.mp u1).resolve_left (by norm_num))
    ((mul_eq_zero.mp u2).resolve_left (mul_ne_zero (by norm_num) ht))
    ((mul_eq_zero.mp u3).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ ht)))

private def waveJet (k : ℂ) (u : Row ℂ) : Row ℂ := jet (k ^ 2) 0 1 u

private def shiftedWaveJet (k δ : ℂ) (u : Row ℂ) : Row ℂ :=
  plus (waveJet k u) (scale δ u)

/-- The horizon leading multiplier, where δ is the derivative shift. -/
def horizonIndicial (k δ : ℂ) (u : Row ℂ) : Row ℂ :=
  minus (shiftedWaveJet k δ (shiftedWaveJet k δ u)) (scale (4 * k ^ 2) u)

private theorem horizon_positive_mode (k δ : ℂ) (u : Row ℂ) :
    mode k (horizonIndicial k δ u) =
      ((δ + 2*k) ^ 2 - 4*k^2) * mode k u := by
  simp only [mode, horizonIndicial, shiftedWaveJet, waveJet, jet, plus, scale, minus]
  ring

private theorem horizon_negative_mode (k δ : ℂ) (u : Row ℂ) :
    mode (-k) (horizonIndicial k δ u) =
      ((δ - 2*k) ^ 2 - 4*k^2) * mode (-k) u := by
  simp only [mode, horizonIndicial, shiftedWaveJet, waveJet, jet, plus, scale, minus]
  ring

private theorem horizon_central_mode (k δ : ℂ) (u : Row ℂ) :
    centralMode k (horizonIndicial k δ u) =
      (δ ^ 2 - 4*k^2) * centralMode k u := by
  simp only [centralMode, horizonIndicial, shiftedWaveJet, waveJet, jet, plus, scale, minus]
  ring

private theorem real_shift_nonzero {x : ℝ} (hx : x ≠ 0) {k : ℂ}
    (hk : k.re = 0) (b : ℝ) : (x : ℂ) + (b : ℂ) * k ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  apply hx
  simpa [Complex.add_re, Complex.mul_re, hk] using hr

/-- A nonzero pole order at the regular horizon cannot hit a daughter resonance. -/
theorem horizon_no_pole (m : ℕ) (hm : 0 < m) (k : ℂ) (hk : k ≠ 0)
    (himag : k.re = 0) (u : Row ℂ)
    (h : horizonIndicial k ((-(m : ℝ) / 2 : ℝ) : ℂ) u = 0) :
    u = 0 := by
  let t : ℝ := -(m : ℝ) / 2
  let δ : ℂ := t
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : t ≠ 0 := by dsimp [t]; linarith
  have hδ (b : ℝ) : δ + (b : ℂ) * k ≠ 0 := real_shift_nonzero ht himag b
  have hp : (δ + 2*k)^2 - 4*k^2 ≠ 0 := by
    rw [show (δ + 2*k)^2-4*k^2 = δ*(δ+4*k) by ring]
    exact mul_ne_zero (by simpa using hδ 0) (by simpa using hδ 4)
  have hn : (δ - 2*k)^2 - 4*k^2 ≠ 0 := by
    rw [show (δ - 2*k)^2-4*k^2 = δ*(δ+(-4)*k) by ring]
    exact mul_ne_zero (by simpa using hδ 0) (by simpa using hδ (-4))
  have h0 : δ^2 - 4*k^2 ≠ 0 := by
    rw [show δ^2-4*k^2 = (δ+(-2)*k)*(δ+2*k) by ring]
    exact mul_ne_zero (by simpa using hδ (-2)) (by simpa using hδ 2)
  change horizonIndicial k δ u = 0 at h
  have p := horizon_positive_mode k δ u
  have n := horizon_negative_mode k δ u
  have c := horizon_central_mode k δ u
  rw [h, show mode k 0 = 0 by simp [mode]] at p
  rw [h, show mode (-k) 0 = 0 by simp [mode]] at n
  rw [h, show centralMode k 0 = 0 by simp [centralMode]] at c
  exact modes_separate k hk u ((mul_eq_zero.mp p.symm).resolve_left hp)
    ((mul_eq_zero.mp n.symm).resolve_left hn) ((mul_eq_zero.mp c.symm).resolve_left h0)

private def originJet (u : Row ℂ) : Row ℂ := jet 12 (-4) 1 u

private def shiftedOriginJet (s : ℂ) (u : Row ℂ) : Row ℂ :=
  plus (originJet u) (scale s u)

/-- The leading origin coefficient at order m+4. -/
def originIndicial (m : ℂ) (u : Row ℂ) : Row ℂ :=
  minus (shiftedOriginJet (2*m+4) (shiftedOriginJet (2*m) u)) (scale 12 u)

private def originMiddle (u : Row ℂ) : ℂ := u.1 - 2*u.2.1 - 12*u.2.2

private theorem origin_modes_separate (u : Row ℂ)
    (hp : mode 2 u = 0) (hn : mode (-6) u = 0) (hc : originMiddle u = 0) :
    u = 0 := by
  dsimp [mode, originMiddle] at *
  apply row_zero
  · linear_combination (9/16 : ℂ) * hp + (1/16 : ℂ) * hn + (3/8 : ℂ) * hc
  · linear_combination (3/16 : ℂ) * hp - (1/16 : ℂ) * hn - (1/8 : ℂ) * hc
  · linear_combination (1/64 : ℂ) * hp + (1/64 : ℂ) * hn - (1/32 : ℂ) * hc

private theorem origin_positive_mode (m : ℂ) (u : Row ℂ) :
    mode 2 (originIndicial m u) = ((2*m+2)*(2*m+10)) * mode 2 u := by
  simp only [mode, originIndicial, shiftedOriginJet, originJet, jet, plus, scale, minus]
  ring

private theorem origin_negative_mode (m : ℂ) (u : Row ℂ) :
    mode (-6) (originIndicial m u) = ((2*m-14)*(2*m-6)) * mode (-6) u := by
  simp only [mode, originIndicial, shiftedOriginJet, originJet, jet, plus, scale, minus]
  ring

private theorem origin_central_mode (m : ℂ) (u : Row ℂ) :
    originMiddle (originIndicial m u) = ((2*m-6)*(2*m+2)) * originMiddle u := by
  simp only [originMiddle, originIndicial, shiftedOriginJet, originJet, jet, plus, scale, minus]
  ring

/-- Only m=3 and m=7 can make this origin multiplier singular for a pole. -/
theorem origin_pole_resonances (m : ℕ) (hm : 0 < m) (u : Row ℂ) (hu : u ≠ 0)
    (h : originIndicial (m : ℂ) u = 0) :
    m = 3 ∨ m = 7 := by
  by_contra hnot
  have h3 : m ≠ 3 := fun h => hnot (Or.inl h)
  have h7 : m ≠ 7 := fun h => hnot (Or.inr h)
  have a : (2*(m : ℂ)+2) ≠ 0 := by exact_mod_cast (show 2*(m : ℤ)+2 ≠ 0 by omega)
  have b : (2*(m : ℂ)+10) ≠ 0 := by exact_mod_cast (show 2*(m : ℤ)+10 ≠ 0 by omega)
  have c : (2*(m : ℂ)-6) ≠ 0 := by exact_mod_cast (show 2*(m : ℤ)-6 ≠ 0 by omega)
  have d : (2*(m : ℂ)-14) ≠ 0 := by exact_mod_cast (show 2*(m : ℤ)-14 ≠ 0 by omega)
  have hp := origin_positive_mode (m : ℂ) u
  have hn := origin_negative_mode (m : ℂ) u
  have hc := origin_central_mode (m : ℂ) u
  rw [h, show mode 2 0 = 0 by simp [mode]] at hp
  rw [h, show mode (-6) 0 = 0 by simp [mode]] at hn
  rw [h, show originMiddle 0 = 0 by simp [originMiddle]] at hc
  exact hu (origin_modes_separate u ((mul_eq_zero.mp hp.symm).resolve_left (mul_ne_zero a b))
    ((mul_eq_zero.mp hn.symm).resolve_left (mul_ne_zero d c))
    ((mul_eq_zero.mp hc.symm).resolve_left (mul_ne_zero c a)))

def infinityLeading (k : ℂ) (u : Row ℂ) : Row ℂ :=
  minus (waveJet k (waveJet k u)) (scale (4*k^2) u)

def infinityNext (k d : ℂ) (u v : Row ℂ) : Row ℂ :=
  plus (infinityLeading k v) (scale (2*d) (waveJet k u))

private theorem infinity_projection (k d : ℂ) (u v : Row ℂ) :
    waveJet k (infinityNext k d u v) = scale (2*d) (waveJet k (waveJet k u)) := by
  apply Prod.ext
  · simp only [waveJet, infinityNext, infinityLeading, jet, plus, minus, scale]
    ring
  · apply Prod.ext <;> simp only [waveJet, infinityNext, infinityLeading, jet, plus, minus, scale] <;> ring

/-- The two highest equations exclude a nonzero leading row at positive degree d. -/
theorem infinity_two_equations (k d : ℂ) (hk : k ≠ 0) (hd : d ≠ 0) (u v : Row ℂ)
    (h₀ : infinityLeading k u = 0) (h₁ : infinityNext k d u v = 0) : u = 0 := by
  have h := infinity_projection k d u v
  rw [h₁, show waveJet k 0 = 0 by apply row_zero <;> simp [waveJet, jet]] at h
  have hz := scale_eq_zero (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hd) h.symm
  rw [infinityLeading, hz, row_zero_minus] at h₀
  apply scale_eq_zero (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (pow_ne_zero 2 hk))
  exact neg_eq_zero.mp h₀

/- These boundary cases keep the order and frequency conditions visible. -/
example : ∃ u : Row ℂ, u ≠ 0 ∧ originIndicial 3 u = 0 ∧ originIndicial 7 u = 0 := by
  refine ⟨(4, -4, 1), ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun v : Row ℂ => v.2.2) h
    norm_num at this
  all_goals
    apply row_zero <;> norm_num [originIndicial, shiftedOriginJet, originJet, jet, plus, minus, scale]

example : ∃ u : Row ℂ, u ≠ 0 ∧ horizonIndicial (1/8) (-1/2) u = 0 := by
  refine ⟨(1/64, 1/4, 1), ?_, ?_⟩
  · intro h
    have := congrArg (fun v : Row ℂ => v.2.2) h
    norm_num at this
  · apply row_zero <;> norm_num [horizonIndicial, shiftedWaveJet, waveJet, jet, plus, minus, scale]

example (k : ℂ) : ∃ u : Row ℂ, u ≠ 0 ∧ infinityLeading k u = 0 := by
  refine ⟨(k^2, 2*k, 1), ?_, ?_⟩
  · intro h
    have := congrArg (fun v : Row ℂ => v.2.2) h
    norm_num at this
  · apply row_zero <;> simp [infinityLeading, waveJet, jet, scale, minus] <;> ring

#print axioms ordinary_pole_forces_leading_term
#print axioms horizon_no_pole
#print axioms origin_pole_resonances
#print axioms infinity_two_equations

end SchwarzschildLaurent
