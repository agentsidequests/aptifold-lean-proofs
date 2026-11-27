module

public import DarbouxGreenKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

/-! # Diagonal contact term in the mixed derivative of the Green kernel

The kernel itself is continuous at the source. Differentiating in the source
coordinate exchanges which factor receives a derivative. The resulting trace
has a jump of `-1` when the evaluation coordinate crosses the source. Testing
its derivative against a function that vanishes at the outer endpoints gives
the diagonal term `-φ(y)` in addition to the two regular integrals.
-/

@[expose] public section

namespace Aptifold.Schwarzschild.Darboux.Green

open Set Filter MeasureTheory
open scoped Interval

noncomputable section

/-- Away from the diagonal, the derivative in the source coordinate acts
on the factor evaluated there. The denominator is fixed. -/
theorem kernel_source_derivative {u v : ℝ → ℂ} {du dv d : ℂ} {x y : ℝ}
    (hu : HasDerivAt u du y) (hv : HasDerivAt v dv y) (hxy : x ≠ y) :
    HasDerivAt (fun s => kernel u v d x s)
      (if x ≤ y then u x * dv / d else du * v x / d) y := by
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [ite_eq_left h.le]
    apply ((hv.const_mul (u x)).div_const d).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact ite_eq_left (mem_Ioi.mp hs).le
  · rw [ite_eq_right h.not_ge]
    apply ((hu.mul_const (v x)).div_const d).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with s hs
    exact ite_eq_right (mem_Iio.mp hs).not_ge

/-- The right trace of the source derivative minus its left trace is `-1`. -/
theorem source_derivative_jump (u v : ℂ × ℂ) (hw : wronskian u v ≠ 0) :
    u.2 * v.1 / wronskian u v - u.1 * v.2 / wronskian u v = -1 := by
  simpa only [derivativeJump, neg_sub] using
    congrArg (fun z : ℂ => -z) (derivative_jump_eq_one u v hw)

/-- Integration by parts across an interior junction includes the jump times
the test function at that junction. The test function vanishes at the two
outer endpoints. -/
theorem piecewise_derivative_pairing {l r dl dr φ dφ : ℝ → ℂ} {a y b : ℝ}
    (hl : ∀ x ∈ [[a, y]], HasDerivWithinAt l (dl x) [[a, y]] x)
    (hr : ∀ x ∈ [[y, b]], HasDerivWithinAt r (dr x) [[y, b]] x)
    (hφl : ∀ x ∈ [[a, y]], HasDerivWithinAt φ (dφ x) [[a, y]] x)
    (hφr : ∀ x ∈ [[y, b]], HasDerivWithinAt φ (dφ x) [[y, b]] x)
    (hil : IntervalIntegrable dl volume a y) (hir : IntervalIntegrable dr volume y b)
    (hiφl : IntervalIntegrable dφ volume a y) (hiφr : IntervalIntegrable dφ volume y b)
    (ha : φ a = 0) (hb : φ b = 0) :
    -((∫ x in a..y, l x * dφ x) + (∫ x in y..b, r x * dφ x)) =
      (∫ x in a..y, dl x * φ x) + (∫ x in y..b, dr x * φ x) + (r y - l y) * φ y := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hl hφl hil hiφl,
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hr hφr hir hiφr, ha, hb]
  ring

/-- The source derivative of the product kernel contributes the local
distributional contact term `-φ(y)` when differentiated in the evaluation
coordinate. `d` is the Wronskian at the source and is held fixed. -/
theorem mixed_derivative_contact_pairing {u v du dv φ dφ : ℝ → ℂ} {a y b : ℝ}
    (hu : ∀ x ∈ [[a, y]], HasDerivWithinAt u (du x) [[a, y]] x)
    (hv : ∀ x ∈ [[y, b]], HasDerivWithinAt v (dv x) [[y, b]] x)
    (hφl : ∀ x ∈ [[a, y]], HasDerivWithinAt φ (dφ x) [[a, y]] x)
    (hφr : ∀ x ∈ [[y, b]], HasDerivWithinAt φ (dφ x) [[y, b]] x)
    (hiu : IntervalIntegrable du volume a y) (hiv : IntervalIntegrable dv volume y b)
    (hiφl : IntervalIntegrable dφ volume a y) (hiφr : IntervalIntegrable dφ volume y b)
    (ha : φ a = 0) (hb : φ b = 0) (hw : wronskian (u y, du y) (v y, dv y) ≠ 0) :
    let d := wronskian (u y, du y) (v y, dv y);
    -((∫ x in a..y, (u x * dv y / d) * dφ x) +
      (∫ x in y..b, (du y * v x / d) * dφ x)) =
      (∫ x in a..y, (du x * dv y / d) * φ x) +
      (∫ x in y..b, (du y * dv x / d) * φ x) - φ y := by
  let d := wronskian (u y, du y) (v y, dv y)
  have hl x hx : HasDerivWithinAt (fun t => u t * dv y / d)
      (du x * dv y / d) [[a, y]] x := ((hu x hx).mul_const (dv y)).div_const d
  have hr x hx : HasDerivWithinAt (fun t => du y * v t / d)
      (du y * dv x / d) [[y, b]] x := ((hv x hx).const_mul (du y)).div_const d
  have hil : IntervalIntegrable (fun x => du x * dv y / d) volume a y := by
    simp only [div_eq_mul_inv]
    exact (hiu.mul_continuousOn continuousOn_const).mul_continuousOn continuousOn_const
  have hir : IntervalIntegrable (fun x => du y * dv x / d) volume y b := by
    simp only [div_eq_mul_inv]
    exact (hiv.continuousOn_mul continuousOn_const).mul_continuousOn continuousOn_const
  dsimp only
  rw [piecewise_derivative_pairing hl hr hφl hφr hil hir hiφl hiφr ha hb]
  have jump := source_derivative_jump (u y, du y) (v y, dv y) hw
  change du y * v y / d - u y * dv y / d = -1 at jump
  rw [jump, neg_one_mul, sub_eq_add_neg]

#print axioms kernel_source_derivative
#print axioms source_derivative_jump
#print axioms piecewise_derivative_pairing
#print axioms mixed_derivative_contact_pairing

end
end Aptifold.Schwarzschild.Darboux.Green
