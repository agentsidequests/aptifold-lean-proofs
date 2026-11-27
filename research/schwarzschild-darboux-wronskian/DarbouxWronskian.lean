module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Wronskian and radial current of the normalized Schwarzschild Darboux map

At a fixed exterior radius a pair contains the wave value and its tortoise
derivative. The factorized radial equations determine the two entries of the
transformed pair. The identities below apply directly to those entries.
-/

@[expose] public section

namespace Aptifold.Schwarzschild.Darboux

noncomputable section

/-- Bilinear Wronskian of two wave jets at one radius. -/
def wronskian (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1

/-- Odd-to-even Darboux value and derivative with incoming normalization `g + k`.
Here `k = iω`, `g` is the special rate, and `W` is the local superpotential. -/
def transform (k g W : ℂ) (u : ℂ × ℂ) : ℂ × ℂ :=
  ((W * u.1 + u.2) / (g + k),
    (W * u.2 + (k ^ 2 + W ^ 2 - g ^ 2) * u.1) / (g + k))

/-- At a shared spectral parameter the bilinear Wronskian acquires a factor
`(g - k) / (g + k)`. This keeps the normalization phase explicit. -/
theorem same_frequency_wronskian (k g W : ℂ) (u v : ℂ × ℂ) (h : g + k ≠ 0) :
    wronskian (transform k g W u) (transform k g W v) =
      ((g - k) / (g + k)) * wronskian u v := by
  unfold wronskian transform
  dsimp only
  field_simp [h]
  ring

/-- Opposite spectral parameters give reciprocal normalization factors.
Their Wronskian is preserved whenever both factors are defined. -/
theorem opposite_frequency_wronskian (k g W : ℂ) (u v : ℂ × ℂ)
    (hplus : g + k ≠ 0) (hminus : g - k ≠ 0) :
    wronskian (transform k g W u) (transform (-k) g W v) = wronskian u v := by
  have hminus' : g + -k ≠ 0 := by simpa only [sub_eq_add_neg] using hminus
  unfold wronskian transform
  dsimp only
  field_simp [hplus, hminus']
  ring

/-- Complex conjugate of a wave jet. -/
def conjugateJet (u : ℂ × ℂ) : ℂ × ℂ := (starRingEnd ℂ u.1, starRingEnd ℂ u.2)

/-- The radial current is `Im(conj(u) · Du)`. The Wronskian convention above
gives `W(u, conj(u)) = -2i · current(u)` for the conjugate pair. -/
def radialCurrent (u : ℂ × ℂ) : ℝ := -(wronskian u (conjugateJet u)).im / 2

/-- The Wronskian convention agrees with the usual imaginary-part current. -/
theorem radialCurrent_eq_im (u : ℂ × ℂ) :
    radialCurrent u = (starRingEnd ℂ u.1 * u.2).im := by
  simp [radialCurrent, wronskian, conjugateJet, Complex.sub_im, Complex.mul_im]
  ring

private theorem conjugate_transform (k g W : ℂ) (u : ℂ × ℂ)
    (hk : starRingEnd ℂ k = -k) (hg : starRingEnd ℂ g = g) (hW : starRingEnd ℂ W = W) :
    conjugateJet (transform k g W u) = transform (-k) g W (conjugateJet u) := by
  apply Prod.ext <;> simp [conjugateJet, transform, hk, hg, hW]

/-- For real frequency and a real superpotential, the normalized map preserves
the real radial current at every radius. A nonzero real rate ensures both
normalizations are defined. -/
theorem real_frequency_radial_current (ω g W : ℝ) (hg : g ≠ 0) (u : ℂ × ℂ) :
    radialCurrent (transform (Complex.I * (ω : ℂ)) (g : ℂ) (W : ℂ) u) =
      radialCurrent u := by
  let k := Complex.I * (ω : ℂ)
  have kre : k.re = 0 := by simp [k, Complex.mul_re]
  have plus : (g : ℂ) + k ≠ 0 := by
    intro h
    exact hg (by simpa [Complex.add_re, kre] using congrArg Complex.re h)
  have minus : (g : ℂ) - k ≠ 0 := by
    intro h
    exact hg (by simpa [Complex.sub_re, kre] using congrArg Complex.re h)
  have hc : starRingEnd ℂ k = -k := by simp [k]
  have transformConj := conjugate_transform k (g : ℂ) (W : ℂ) u hc (by simp) (by simp)
  change radialCurrent (transform k (g : ℂ) (W : ℂ) u) = radialCurrent u
  unfold radialCurrent
  rw [transformConj, opposite_frequency_wronskian k _ _ _ _ plus minus]

-- An outgoing unit plane wave has positive current in the paper's convention.
example : radialCurrent (1, Complex.I) = 1 := by
  norm_num [radialCurrent, wronskian, conjugateJet, Complex.sub_im]

-- The same-frequency pairing can change, even with real frequency and rate.
example : wronskian (transform Complex.I 1 0 (1, 0))
    (transform Complex.I 1 0 (0, 1)) = -Complex.I := by
  have h : (1 : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    norm_num [Complex.add_re] at he
  rw [same_frequency_wronskian _ _ _ _ _ h]
  simp [wronskian]
  apply (div_eq_iff h).2
  calc
    (1 : ℂ) - Complex.I = -Complex.I - Complex.I ^ 2 := by rw [Complex.I_sq]; ring
    _ = -Complex.I * (1 + Complex.I) := by ring

#print axioms same_frequency_wronskian
#print axioms opposite_frequency_wronskian
#print axioms radialCurrent_eq_im
#print axioms real_frequency_radial_current

end
end Aptifold.Schwarzschild.Darboux
