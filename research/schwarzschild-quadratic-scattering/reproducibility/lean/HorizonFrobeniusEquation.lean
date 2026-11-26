import HorizonFrobeniusSeries
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The convergent horizon series solves the differential equation
after the ingoing carrier is factored out. -/
namespace SchwarzschildLaurent.Horizon

open Filter FormalMultilinearSeries
open scoped Topology

noncomputable section

private abbrev ScalarSeries (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop :=
  HasFPowerSeriesAt f (ofScalars ℂ a) 0

private def derivCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ)+1)*a (n+1)

private def shiftCoefficients (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => a n

private theorem derivative_series {f : ℂ → ℂ} {a : ℕ → ℂ} (h : ScalarSeries f a) :
    ScalarSeries (deriv f) (derivCoefficients a) := by
  obtain ⟨r,hr⟩ := h
  let eval := ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have series := (eval.comp_hasFPowerSeriesOnBall hr.fderiv).hasFPowerSeriesAt
  have coefficient (n : ℕ) :
      (eval.compFormalMultilinearSeries (ofScalars ℂ a).derivSeries).coeff n =
        derivCoefficients a n := by
    change (ofScalars ℂ a).derivSeries.coeff n (1 : ℂ) = _
    rw [derivSeries_coeff_one, coeff_ofScalars]
    simp [derivCoefficients, nsmul_eq_mul, Nat.cast_succ]
  unfold ScalarSeries
  apply hasFPowerSeriesAt_iff.mpr
  have sum := hasFPowerSeriesAt_iff.mp series
  simpa only [coefficient, coeff_ofScalars, zero_add, Function.comp_apply, eval,
    ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv] using sum

private theorem shift_series {f : ℂ → ℂ} {a : ℕ → ℂ} (h : ScalarSeries f a) :
    ScalarSeries (fun s => s*f s) (shiftCoefficients a) := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [hasFPowerSeriesAt_iff.mp h] with s hs
  simp only [zero_add, coeff_ofScalars, smul_eq_mul] at hs ⊢
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, shiftCoefficients, pow_zero, one_mul, pow_succ', mul_assoc, sub_zero]
    using hs.mul_left s

private theorem scale_series {f : ℂ → ℂ} {a : ℕ → ℂ} (c : ℂ) (h : ScalarSeries f a) :
    ScalarSeries (c • f) (c • a) := by
  simpa only [ScalarSeries, ofScalars_smul] using (h.const_smul (c := c))

private theorem add_series {f g : ℂ → ℂ} {a b : ℕ → ℂ} (h : ScalarSeries f a)
    (j : ScalarSeries g b) : ScalarSeries (f+g) (a+b) := by
  simpa only [ScalarSeries, ofScalars_add] using h.add j

/-- The Regge–Wheeler equation for \(H(s)\), after removal of
\(e^{-kx}\) and clearing the radial denominators. -/
def horizonResidual (k L : ℂ) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  s*(s+2)^2*deriv (deriv H) s +
    (2*(s+2)-2*k*(s+2)^3)*deriv H s + (6-L*(s+2))*H s

private def residualCoefficients (k L : ℂ) (a : ℕ → ℂ) : ℕ → ℂ :=
  let d := derivCoefficients a
  let dd := derivCoefficients d
  let shift := shiftCoefficients
  ((4 : ℂ) • shift dd + (4 : ℂ) • shift (shift dd) + shift (shift (shift dd))) +
    ((4-16*k) • d + (2-24*k) • shift d + (-12*k) • shift (shift d) +
      (-2*k) • shift (shift (shift d))) +
    ((6-2*L) • a + (-L) • shift a)

private theorem residual_series (k L : ℂ) {H : ℂ → ℂ} {a : ℕ → ℂ} (h : ScalarSeries H a) :
    ScalarSeries (horizonResidual k L H) (residualCoefficients k L a) := by
  have hd := derivative_series h
  have hdd := derivative_series hd
  have p := add_series
    (add_series (scale_series 4 (shift_series hdd)) (scale_series 4 (shift_series (shift_series hdd))))
    (shift_series (shift_series (shift_series hdd)))
  have q := add_series
    (add_series (add_series (scale_series (4-16*k) hd) (scale_series (2-24*k) (shift_series hd)))
      (scale_series (-12*k) (shift_series (shift_series hd))))
    (scale_series (-2*k) (shift_series (shift_series (shift_series hd))))
  have r := add_series (scale_series (6-2*L) h) (scale_series (-L) (shift_series h))
  have full := add_series (add_series p q) r
  convert full using 1
  · funext s
    simp only [horizonResidual, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rfl

private theorem previous_coefficient (k L : ℂ) (n : ℕ) :
    (horizonState k L (n+1)).2.1 = horizonCoefficient k L n := rfl

private theorem older_coefficient (k L : ℂ) (n : ℕ) :
    (horizonState k L (n+2)).2.2 = horizonCoefficient k L n := rfl

private theorem missing_previous (k L : ℂ) : (horizonState k L 0).2.1 = 0 := rfl
private theorem missing_older (k L : ℂ) : (horizonState k L 0).2.2 = 0 := rfl

private theorem residual_coefficient_exact (k L : ℂ) (n : ℕ) :
    residualCoefficients k L (horizonCoefficient k L) n =
      horizonLeading k n*horizonCoefficient k L (n+1) +
        horizonMiddle k L n*(horizonState k L n).1 +
        horizonPrevious k L n*(horizonState k L n).2.1 +
        horizonOlder k n*(horizonState k L n).2.2 := by
  change residualCoefficients k L (horizonCoefficient k L) n =
    horizonLeading k n*horizonCoefficient k L (n+1)+horizonMiddle k L n*horizonCoefficient k L n+
    horizonPrevious k L n*(horizonState k L n).2.1+horizonOlder k n*(horizonState k L n).2.2
  rcases n with _|_|_|n <;>
    simp only [residualCoefficients, derivCoefficients, shiftCoefficients, horizonLeading, horizonMiddle,
      horizonPrevious, horizonOlder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, previous_coefficient,
      older_coefficient, missing_previous, missing_older, Nat.cast_zero, Nat.cast_succ]
  all_goals
    try rw [show (horizonState k L 1).2.2 = 0 from rfl]
    ring

theorem ingoing_envelope_equation (k L : ℂ) (ki : k.re = 0) :
    ∀ᶠ s in 𝓝 (0 : ℂ), horizonResidual k L (ingoingEnvelope k L) s = 0 := by
  have series := residual_series k L (ingoing_has_power_series k L ki)
  have vanish : residualCoefficients k L (horizonCoefficient k L) = 0 := by
    funext n
    rw [residual_coefficient_exact]
    exact horizon_coefficient_recurrence k L ki n
  rw [ScalarSeries, vanish, ofScalars_series_eq_zero_of_scalar_zero] at series
  filter_upwards [hasFPowerSeriesAt_iff.mp series] with s hs
  have zero : HasSum (fun _ : ℕ => (0 : ℂ)) (horizonResidual k L (ingoingEnvelope k L) s) := by
    simpa [FormalMultilinearSeries.coeff] using hs
  exact zero.unique (hasSum_zero)

theorem ingoing_envelope_derivative (k L : ℂ) (ki : k.re = 0) :
    deriv (ingoingEnvelope k L) 0 = (L-3)/(2*(1-4*k)) := by
  rw [(ingoing_has_power_series k L ki).deriv]
  change (ofScalars ℂ (horizonCoefficient k L)).coeff 1 = _
  rw [coeff_ofScalars]
  have hk : 1-4*k ≠ 0 := by
    intro h
    apply horizon_leading_ne_zero k ki 0
    simp [horizonLeading, h]
  simp only [horizonCoefficient, horizonState, horizonLeading, horizonMiddle, Nat.cast_zero]
  field_simp [hk]
  ring

#print axioms ingoing_envelope_equation
#print axioms ingoing_envelope_derivative

end
end SchwarzschildLaurent.Horizon
