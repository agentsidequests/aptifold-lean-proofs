module

public import DarbouxWronskian
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! # Green-kernel matching under the Schwarzschild Darboux map

For fixed source coordinate `y`, the product kernel uses the left solution at
the smaller tortoise coordinate and the right solution at the larger one.
The Wronskian at `y` normalizes the one-sided derivative jump to one.
-/

@[expose] public section

namespace Aptifold.Schwarzschild.Darboux.Green

open Set

noncomputable section

/-- Product kernel constructed from left and right profiles, with a fixed denominator. -/
def kernel (u v : ℝ → ℂ) (d : ℂ) (x y : ℝ) : ℂ :=
  if x ≤ y then u x * v y / d else u y * v x / d

/-- The derivative on the left of the source coordinate. -/
theorem kernel_left_derivative {u v : ℝ → ℂ} {du : ℂ} {y : ℝ} (d : ℂ)
    (hu : HasDerivAt u du y) :
    HasDerivWithinAt (fun x => kernel u v d x y) (du * v y / d) (Iic y) y := by
  refine ((hu.mul_const (v y)).div_const d).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact ite_eq_left (show x ≤ y from hx)
  · exact ite_eq_left le_rfl

/-- The derivative on the right of the source coordinate. -/
theorem kernel_right_derivative {u v : ℝ → ℂ} {dv : ℂ} {y : ℝ} (d : ℂ)
    (hv : HasDerivAt v dv y) :
    HasDerivWithinAt (fun x => kernel u v d x y) (u y * dv / d) (Ici y) y := by
  refine ((hv.const_mul (u y)).div_const d).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    by_cases h : x ≤ y
    · have eq : x = y := le_antisymm h hx
      simp [eq, kernel]
    · exact ite_eq_right h
  · exact ite_eq_left le_rfl

/-- The left and right branches meet continuously at the source. -/
theorem kernel_continuous_at_source {u v : ℝ → ℂ} {du dv : ℂ} {y : ℝ} (d : ℂ)
    (hu : HasDerivAt u du y) (hv : HasDerivAt v dv y) :
    ContinuousAt (fun x => kernel u v d x y) y := by
  have h := (kernel_left_derivative d hu).continuousWithinAt.union
    (kernel_right_derivative d hv).continuousWithinAt
  simpa only [Iic_union_Ici, continuousWithinAt_univ] using h

/-- Right derivative minus left derivative using the Wronskian at the source. -/
def derivativeJump (u v : ℂ × ℂ) : ℂ :=
  u.1 * v.2 / wronskian u v - u.2 * v.1 / wronskian u v

/-- Normalization gives a positive unit jump for every independent jet pair. -/
theorem derivative_jump_eq_one (u v : ℂ × ℂ) (h : wronskian u v ≠ 0) :
    derivativeJump u v = 1 := by
  unfold derivativeJump
  rw [← sub_div]
  exact div_self h

/-- Dividing by the Wronskian produces a continuous kernel whose two actual
one-sided derivatives differ by one. -/
theorem green_matching {u v : ℝ → ℂ} {du dv : ℂ} {y : ℝ}
    (hu : HasDerivAt u du y) (hv : HasDerivAt v dv y)
    (hw : wronskian (u y, du) (v y, dv) ≠ 0) :
    let d := wronskian (u y, du) (v y, dv)
    let G := fun x => kernel u v d x y
    ContinuousAt G y ∧ ∃ left right : ℂ,
      HasDerivWithinAt G left (Iic y) y ∧
      HasDerivWithinAt G right (Ici y) y ∧ right - left = 1 := by
  let d := wronskian (u y, du) (v y, dv)
  exact ⟨kernel_continuous_at_source d hu hv, du * v y / d, u y * dv / d,
    kernel_left_derivative d hu, kernel_right_derivative d hv,
    derivative_jump_eq_one (u y, du) (v y, dv) hw⟩

/-- The Darboux-transformed jet pair has the same positive unit jump, provided
the Wronskian and both parity normalizations are nonzero. -/
theorem transformed_derivative_jump_eq_one (k g W : ℂ) (u v : ℂ × ℂ)
    (hp : g + k ≠ 0) (hm : g - k ≠ 0) (hw : wronskian u v ≠ 0) :
    derivativeJump (transform k g W u) (transform k g W v) = 1 := by
  apply derivative_jump_eq_one
  rw [same_frequency_wronskian k g W u v hp]
  exact mul_ne_zero (div_ne_zero hm hp) hw

/-- Keeping the original Wronskian under the transformed numerator gives the
wrong jump in general. This identity makes its extra factor explicit. -/
theorem jump_with_original_wronskian (k g W : ℂ) (u v : ℂ × ℂ)
    (hp : g + k ≠ 0) (hw : wronskian u v ≠ 0) :
    let U := transform k g W u
    let V := transform k g W v
    U.1 * V.2 / wronskian u v - U.2 * V.1 / wronskian u v = (g - k) / (g + k) := by
  dsimp only
  rw [← sub_div]
  change wronskian (transform k g W u) (transform k g W v) / wronskian u v = _
  rw [same_frequency_wronskian k g W u v hp, mul_div_assoc, div_self hw, mul_one]

/-- Turning the normalized Darboux operation on both value factors into a
kernel requires the reciprocal Wronskian factor `(g+k)/(g-k)`. The two product
branches use the same fixed source denominator. -/
theorem transformed_kernel_normalization (k g : ℂ) (W : ℝ → ℂ)
    (u v : ℝ → ℂ × ℂ) (x y : ℝ)
    (hp : g + k ≠ 0) (hm : g - k ≠ 0) (hw : wronskian (u y) (v y) ≠ 0) :
    let U := fun t => (transform k g (W t) (u t)).1
    let V := fun t => (transform k g (W t) (v t)).1
    kernel U V (wronskian (transform k g (W y) (u y)) (transform k g (W y) (v y))) x y =
      ((g + k) / (g - k)) * kernel U V (wronskian (u y) (v y)) x y := by
  dsimp only
  rw [same_frequency_wronskian k g (W y) (u y) (v y) hp]
  have normalize (a b : ℂ) :
      a * b / (((g - k) / (g + k)) * wronskian (u y) (v y)) =
        ((g + k) / (g - k)) * (a * b / wronskian (u y) (v y)) := by
    field_simp [hp, hm, hw]
  unfold kernel
  split <;> exact normalize _ _

example : derivativeJump (1, 0) (0, 1) = 1 := by
  norm_num [derivativeJump, wronskian]

#print axioms kernel_continuous_at_source
#print axioms derivative_jump_eq_one
#print axioms green_matching
#print axioms transformed_derivative_jump_eq_one
#print axioms jump_with_original_wronskian
#print axioms transformed_kernel_normalization

end
end Aptifold.Schwarzschild.Darboux.Green
