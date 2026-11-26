import ExteriorProjectedSource

/-! Transport the rational coefficient operator to ordinary derivatives
on a real exterior wave. -/
namespace SchwarzschildMixtures.Strain

open SchwarzschildLaurent SchwarzschildLaurent.Exterior SchwarzschildLaurent.Outgoing

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

private theorem radial_factor_value (r : ℝ) (hr : 2 < r) :
    RadiusValue (r : ℂ) radialFactor (radiusLapse r) := by
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  have two : RadiusValue (r : ℂ) (2:ℂᵣ) 2 := by
    simpa only [map_ofNat] using RadiusValue.const (r : ℂ) 2
  have v := RadiusValue.radius (r : ℂ)
  exact (v.sub two).div v nz

private theorem potential_value (constant L : ℂ) (r : ℝ) (hr : 2 < r) :
    RadiusValue (r : ℂ) (Cᵣ constant+oddPotential L)
      (constant+radiusLapse r*(L/(r : ℂ)^2-6/(r : ℂ)^3)) := by
  have nz : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by linarith)
  have radius := RadiusValue.radius (r : ℂ)
  have six : RadiusValue (r : ℂ) (6:ℂᵣ) 6 := by
    simpa only [map_ofNat] using RadiusValue.const (r : ℂ) 6
  have first := (RadiusValue.const (r : ℂ) L).div (radius.pow 2) (pow_ne_zero 2 nz)
  have second := six.div (radius.pow 3) (pow_ne_zero 3 nz)
  exact (RadiusValue.const (r : ℂ) constant).add ((radial_factor_value r hr).mul (first.sub second))

private theorem unscaled_step_values (L k : ℂ) (p : Row ℂᵣ) (r : ℝ) (hr : 2 < r)
    (h : RegularRow r p) :
    RowValues r (unscaledStep L k p)
      (quadraticJetCoefficients (readRow p r)
        (scale (radiusLapse r) (readRow (rationalRowDerivative p) r)) (rwPotential k L r)) := by
  have first := RowValues.scale (radial_factor_value r hr) h.derivative
  have second := RowValues.jet (potential_value (k^2) L r hr)
    (RadiusValue.zero (r : ℂ)) (RadiusValue.one (r : ℂ)) h
  let p₀ := readRow p r
  let dp := scale (radiusLapse r) (readRow (rationalRowDerivative p) r)
  let v := rwPotential k L r
  have coeff : plus dp (jet v 0 1 p₀) = quadraticJetCoefficients p₀ dp v := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [plus,jet,quadraticJetCoefficients,zero_mul,mul_zero,one_mul,add_zero] <;> ring
  exact coeff ▸ first.plus second

/-- One rational jet step is exactly the tortoise derivative of the
quadratic field evaluated on the real parent and its jet. -/
theorem unscaled_step_derivative (L k : ℂ) (p : Row ℂᵣ) (u du : ℝ → ℂ)
    (parent : RadialEquation radiusLapse (rwPotential k L) 0 u du)
    {r : ℝ} (hr : 2 < r) (h : RegularRow r p) :
    HasDerivAt (waveRowValue p u du) (waveRowValue (unscaledStep L k p) u du r/radiusLapse r) r := by
  have f0 := exterior_lapse_nonzero hr
  let dc := fun s => scale (radiusLapse s) (readRow (rationalRowDerivative p) s)
  have A : HasDerivAt (fun s => (readRow p s).1) ((dc r).1/radiusLapse r) r := by
    simpa only [dc,scale,readRow,mapRow,rationalRowDerivative,mul_div_cancel_left₀ _ f0] using
      radial_eval_derivative h.1
  have B : HasDerivAt (fun s => (readRow p s).2.1) ((dc r).2.1/radiusLapse r) r := by
    simpa only [dc,scale,readRow,mapRow,rationalRowDerivative,mul_div_cancel_left₀ _ f0] using
      radial_eval_derivative h.2.1
  have C : HasDerivAt (fun s => (readRow p s).2.2) ((dc r).2.2/radiusLapse r) r := by
    simpa only [dc,scale,readRow,mapRow,rationalRowDerivative,mul_div_cancel_left₀ _ f0] using
      radial_eval_derivative h.2.2
  change HasDerivAt (waveRowValue p u du)
    (quadraticValue (readRow (unscaledStep L k p) r) (u r) (du r)/radiusLapse r) r
  rw [(unscaled_step_values L k p r hr h).read_eq]
  exact quadratic_has_derivative radiusLapse (rwPotential k L) u du (readRow p) dc parent hr f0 A B C

private theorem unscaled_operator_read (L M k : ℂ) (p : Row ℂᵣ) (r : ℝ) (hr : 2 < r)
    (h : RegularRow r p) :
    readRow (unscaledOperator L M k p) r =
      minus (readRow (unscaledStep L k (unscaledStep L k p)) r)
        (scale (rwPotential (2*k) M r) (readRow p r)) := by
  have q₁ := (unscaled_step_values L k p r hr h).regular
  have q₂ := (unscaled_step_values L k (unscaledStep L k p) r hr q₁).regular
  have rate : (2*k)^2 = 4*k^2 := by ring
  have v : RadiusValue (r : ℂ) (Cᵣ (4*k^2)+oddPotential M) (rwPotential (2*k) M r) := by
    rw [rwPotential,rate]
    exact potential_value (4*k^2) M r hr
  exact (q₂.minus (RowValues.scale v h)).read_eq

/-- Realize an exact rational row identity as a forced equation on an
arbitrary homogeneous exterior parent. -/
theorem unscaled_forced_radial_equation (L M k : ℂ) (p s : Row ℂᵣ) (u du : ℝ → ℂ)
    (parent : RadialEquation radiusLapse (rwPotential k L) 0 u du)
    (field : ∀ r : ℝ, 2 < r → RegularRow r p)
    (source : unscaledOperator L M k p = s) :
    RadialEquation radiusLapse (rwPotential (2*k) M) (waveRowValue s u du)
      (waveRowValue p u du) (waveRowValue (unscaledStep L k p) u du) := by
  constructor
  · intro r hr
    exact unscaled_step_derivative L k p u du parent hr (field r hr)
  · intro r hr
    let q := unscaledStep L k p
    let v := rwPotential (2*k) M r
    have h := (unscaled_step_values L k p r hr (field r hr)).regular
    apply (unscaled_step_derivative L k q u du parent hr h).congr_deriv
    have value : waveRowValue s u du r = waveRowValue (unscaledStep L k q) u du r-v*waveRowValue p u du r := by
      have exactRow := unscaled_operator_read L M k p r hr (field r hr)
      rw [source] at exactRow
      unfold waveRowValue
      rw [exactRow]
      simp only [minus,scale,v,q,quadraticValue]
      ring
    rw [value]
    change _ = (v*waveRowValue p u du r +
      (waveRowValue (unscaledStep L k q) u du r-v*waveRowValue p u du r))/radiusLapse r
    ring

#print axioms unscaled_step_derivative
#print axioms unscaled_forced_radial_equation

end
end SchwarzschildMixtures.Strain
