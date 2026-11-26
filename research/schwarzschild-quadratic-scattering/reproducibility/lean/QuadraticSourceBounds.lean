import LinearWaveEndpointBounds
import ExteriorProjectedSource

/-! Endpoint estimates for a quadratic source whose unscaled coefficients
share a single nonvanishing polynomial denominator. -/
namespace SchwarzschildMixtures.Strain

open Polynomial Filter Set
open SchwarzschildLaurent SchwarzschildLaurent.Exterior SchwarzschildLaurent.LinearWave
open SchwarzschildLaurent.Outgoing
open scoped Topology

noncomputable section

def polynomialQuadraticSource (p : Row ℂ[X]) (q : ℂ[X]) (u du : ℝ → ℂ) (r : ℝ) : ℂ :=
  quadraticValue (mapRow (fun v => v.eval (r : ℂ)) p) (u r) (du r)/q.eval (r : ℂ)

theorem polynomial_source_from_fraction (p : Row ℂ[X]) (q : ℂ[X]) (u du : ℝ → ℂ) (r : ℝ)
    (nonzero : q.eval (r : ℂ) ≠ 0) :
    waveRowValue (fractionRow p q) u du r = polynomialQuadraticSource p q u du r := by
  have values : RowValues r (fractionRow p q) (mapRow (fun v : ℂ[X] =>
      v.eval (r : ℂ)/q.eval (r : ℂ)) p) :=
    ⟨RadiusValue.fraction _ _ nonzero,RadiusValue.fraction _ _ nonzero,RadiusValue.fraction _ _ nonzero⟩
  rw [waveRowValue,values.read_eq]
  simp only [polynomialQuadraticSource,quadraticValue,mapRow]
  ring

theorem polynomial_source_continuous (p : Row ℂ[X]) (q : ℂ[X]) (u du : ℝ → ℂ)
    (q0 : ∀ r : ℝ, 2 < r → q.eval (r : ℂ) ≠ 0)
    (uc : ContinuousOn u (Ioi (2 : ℝ))) (duc : ContinuousOn du (Ioi (2 : ℝ))) :
    ContinuousOn (polynomialQuadraticSource p q u du) (Ioi (2 : ℝ)) := by
  have ev (a : ℂ[X]) : ContinuousOn (fun r : ℝ => a.eval (r : ℂ)) (Ioi (2 : ℝ)) :=
    (a.continuous.comp Complex.continuous_ofReal).continuousOn
  unfold polynomialQuadraticSource quadraticValue mapRow
  exact ((((ev p.1).mul (uc.pow 2)).add (((ev p.2.1).mul uc).mul duc)).add
    ((ev p.2.2).mul (duc.pow 2))).div (ev q) q0

theorem inverse_lapse_continuous : ContinuousOn (fun r => (radiusLapse r)⁻¹) (Ioi (2 : ℝ)) := by
  have cast : ContinuousOn (fun r : ℝ => (r : ℂ)) (Ioi (2 : ℝ)) := Complex.continuous_ofReal.continuousOn
  have lapse : ContinuousOn radiusLapse (Ioi (2 : ℝ)) := by
    unfold radiusLapse
    exact (cast.sub continuousOn_const).div cast (fun r hr =>
      Complex.ofReal_ne_zero.mpr (show r ≠ 0 by have : 2 < r := hr; linarith))
  exact lapse.inv₀ (fun r hr => exterior_lapse_nonzero hr)

/-- If the ingoing contraction vanishes at the horizon, division by
the lapse still leaves a bounded source there. -/
theorem polynomial_source_horizon_bound (p : Row ℂ[X]) (q : ℂ[X]) (k L a : ℂ)
    (ki : k.re = 0) (q0 : q.eval (2 : ℂ) ≠ 0)
    (compatibility : p.1.eval 2-k*p.2.1.eval 2+k^2*p.2.2.eval 2 = 0)
    (u : IngoingWaveData k L a) :
    ∃ C : ℝ, ∀ᶠ r in 𝓝[>] (2 : ℝ),
      ‖polynomialQuadraticSource p q u.value u.jet r/radiusLapse r‖ ≤ C := by
  let H := horizonEnvelope k L a
  let m := fun r => phase (-k) (realTortoise r)
  obtain ⟨analytic,wave⟩ := normalized_horizon_envelope k L a ki u.value u.horizon
  have jet := ingoing_exterior_jet k m u.value u.jet H analytic (exterior_carrier_derivative k) wave u.equation.value
  let P := p.1-C k*p.2.1+C (k^2)*p.2.2
  have root : P.eval 2 = 0 := by simp [P,eval_mul,compatibility]
  obtain ⟨b,factor⟩ := (dvd_iff_isRoot.mpr root : X-C (2:ℂ) ∣ P)
  let F := fun z : ℂ => (z-2)/z
  let G := fun z : ℂ =>
    (z*b.eval z*H z^2 + (p.2.1.eval z-2*k*p.2.2.eval z)*H z*deriv H z+
      F z*p.2.2.eval z*(deriv H z)^2)/q.eval z
  have h : ContinuousAt H (2 : ℂ) := analytic.continuousAt
  have dh : ContinuousAt (deriv H) (2 : ℂ) := analytic.deriv.continuousAt
  have ff : ContinuousAt F (2 : ℂ) :=
    (continuousAt_id.sub continuousAt_const).div continuousAt_id (by norm_num)
  have gcont : ContinuousAt G (2 : ℂ) :=
    (((continuousAt_id.mul b.continuousAt).mul (h.pow 2)).add
      (((p.2.1.continuousAt.sub (continuousAt_const.mul p.2.2.continuousAt)).mul h).mul dh) |>.add
      ((ff.mul p.2.2.continuousAt).mul (dh.pow 2))).div q.continuousAt q0
  have qcont := q.continuousAt.eventually_ne q0
  have gLimit := gcont.tendsto.comp exterior_horizon_radius
  obtain ⟨B,_,bounded⟩ := eventually_bounded_norm_of_limit gLimit
  refine ⟨B,?_⟩
  filter_upwards [wave,jet,bounded,exterior_horizon_radius.eventually qcont,
    self_mem_nhdsWithin (s := Ioi (2 : ℝ))] with r hu hd hb hq hr
  have r0 : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by have : 2 < r := hr; linarith)
  have gap : (r : ℂ)-2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show 2 < r from hr).ne')
  have hq' : q.eval (r : ℂ) ≠ 0 := hq
  have rowEq := congrArg (Polynomial.eval (r : ℂ)) factor
  have first :
      p.1.eval (r : ℂ) = (r-2 : ℂ)*b.eval (r : ℂ)+k*p.2.1.eval (r : ℂ)-k^2*p.2.2.eval (r : ℂ) := by
    simp only [P,eval_add,eval_sub,eval_mul,eval_C,eval_X] at rowEq
    linear_combination rowEq
  have product :
      polynomialQuadraticSource p q u.value u.jet r/radiusLapse r = m r^2*G (r : ℂ) := by
    simp only [polynomialQuadraticSource,quadraticValue,mapRow,hu,hd,first]
    simp only [horizonDerivative,radiusLapse,G,F,m]
    field_simp [r0,gap,hq']
    ring
  have unit : ‖m r‖ = 1 := phase_norm (-k) (by simp [ki]) (realTortoise r)
  rw [product,norm_mul,norm_pow,unit,one_pow,one_mul]
  exact hb

private theorem quadratic_value_bound (p : Row ℂ) (u du : ℂ) (A B : ℝ)
    (a0 : 0 ≤ A) (b0 : 0 ≤ B) (ha : ‖p.1‖ ≤ A) (hb : ‖p.2.1‖ ≤ A) (hc : ‖p.2.2‖ ≤ A)
    (hu : ‖u‖ ≤ B) (hd : ‖du‖ ≤ B) :
    ‖quadraticValue p u du‖ ≤ 3*A*B^2 := by
  have a : ‖p.1*u^2‖ ≤ A*B^2 := by simp only [norm_mul,norm_pow]; gcongr
  have b : ‖p.2.1*u*du‖ ≤ A*B^2 := by simp only [norm_mul,pow_two,mul_assoc]; gcongr
  have c : ‖p.2.2*du^2‖ ≤ A*B^2 := by simp only [norm_mul,norm_pow]; gcongr
  unfold quadraticValue
  calc
    _ ≤ ‖p.1*u^2+p.2.1*u*du‖+‖p.2.2*du^2‖ := norm_add_le _ _
    _ ≤ ‖p.1*u^2‖+‖p.2.1*u*du‖+‖p.2.2*du^2‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by linarith

/-- Two powers of degree gap give an inverse-square source bound. -/
theorem polynomial_source_infinity_bound (p : Row ℂ[X]) (q : ℂ[X]) (d : ℕ) (k L a : ℂ)
    (hk : k ≠ 0) (ki : k.re = 0)
    (degree : q.natDegree = d+2) (q0 : q ≠ 0)
    (dA : p.1.natDegree ≤ d) (dB : p.2.1.natDegree ≤ d) (dC : p.2.2.natDegree ≤ d)
    (u : IngoingWaveData k L a) :
    ∃ C : ℝ, ∀ᶠ r in atTop,
      ‖polynomialQuadraticSource p q u.value u.jet r/radiusLapse r‖ ≤ C*r^(-2 : ℝ) := by
  obtain ⟨A,a0,ha⟩ := eventually_bounded_norm_of_limit (polynomial_quotient_scaled_limit p.1 q d 2 dA degree q0)
  obtain ⟨B,b0,hb⟩ := eventually_bounded_norm_of_limit (polynomial_quotient_scaled_limit p.2.1 q d 2 dB degree q0)
  obtain ⟨C,c0,hc⟩ := eventually_bounded_norm_of_limit (polynomial_quotient_scaled_limit p.2.2 q d 2 dC degree q0)
  obtain ⟨W,w0,wave⟩ := (ingoing_wave_endpoint_bounds hk ki u).2
  obtain ⟨F,f0,fac⟩ := eventually_bounded_norm_of_limit (lapse_tends_to_one.inv₀ one_ne_zero)
  let M := max A (max B C)
  have m0 : 0 ≤ M := a0.le.trans (le_max_left _ _)
  refine ⟨(3*M*W^2)*F,?_⟩
  filter_upwards [ha,hb,hc,wave,fac,eventually_gt_atTop (0 : ℝ)] with r ra rb rc rw rf rpos
  let P := mapRow (fun v : ℂ[X] => (r : ℂ)^2*(v.eval (r : ℂ)/q.eval (r : ℂ))) p
  have bound := quadratic_value_bound P (u.value r) (u.jet r) M W m0 w0.le
    (ra.trans (le_max_left _ _)) (rb.trans ((le_max_left _ _).trans (le_max_right _ _)))
    (rc.trans ((le_max_right _ _).trans (le_max_right _ _))) rw.1 rw.2
  have scale :
      (r : ℂ)^2*(polynomialQuadraticSource p q u.value u.jet r/radiusLapse r) =
        quadraticValue P (u.value r) (u.jet r)*(radiusLapse r)⁻¹ := by
    simp only [P,polynomialQuadraticSource,quadraticValue,mapRow,div_eq_mul_inv]
    ring
  have normed := mul_le_mul bound rf (norm_nonneg _) (by positivity : 0 ≤ 3*M*W^2)
  rw [← norm_mul,← scale,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos rpos] at normed
  change ‖polynomialQuadraticSource p q u.value u.jet r/radiusLapse r‖ ≤ (3*M*W^2)*F*r^(-2 : ℝ)
  rw [Real.rpow_neg rpos.le,Real.rpow_two,← div_eq_mul_inv]
  exact (le_div_iff₀ (sq_pos_of_pos rpos)).mpr (by simpa only [mul_comm] using normed)

#print axioms polynomial_source_from_fraction
#print axioms polynomial_source_continuous
#print axioms polynomial_source_horizon_bound
#print axioms polynomial_source_infinity_bound

end
end SchwarzschildMixtures.Strain
