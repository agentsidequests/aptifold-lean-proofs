import RiccatiInfinity

/-! Orders of the discriminant in a possible quadratic Riccati extension. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative
local notation "D" => tortoiseDerivative

theorem QuadraticRiccati.nonzero {h k : ℂ} {a b : ℂᵣ} (q : QuadraticRiccati h k a b) : b≠0 := by
  intro hz
  exact q.nonsquare ⟨0, by simp [hz]⟩

private theorem factor_value {x : ℂ} (hx : x ≠ 0) : RadiusValue x radialFactor ((x-2)/x) := by
  have two : RadiusValue x (2:ℂᵣ) 2 := by simpa only [map_ofNat] using RadiusValue.const x 2
  exact ((RadiusValue.radius x).sub two).div (RadiusValue.radius x) hx

private theorem parentTerm_value (h k x : ℂ) (hx : x ≠ 0) :
    RadiusValue x (parentTerm h k) (k^2+(x-2)/x*(h/x^2-6/x^3)) := by
  have six : RadiusValue x (6:ℂᵣ) 6 := by simpa only [map_ofNat] using RadiusValue.const x 6
  have r := RadiusValue.radius x
  exact (RadiusValue.const x (k^2)).add ((factor_value hx).mul
    (((RadiusValue.const x h).div (r.pow 2) (pow_ne_zero 2 hx)).sub
      (six.div (r.pow 3) (pow_ne_zero 3 hx))))

private theorem four_value (x : ℂ) : RadiusValue x (4:ℂᵣ) 4 := by
  simpa only [map_ofNat] using RadiusValue.const x 4

/-- The discriminant equation determines the mean as a log derivative. -/
private theorem mean_times_coordinate {x : ℂ} {a b v ν : ℂᵣ} {m : ℤ} (hv : v≠0)
    (factored : b=(coordinate x)^m*v) (equation : ν*δ b = -4*a*b) :
    let t := coordinate x
    t*a = -(ν*((m:ℂᵣ)+t*δ v/v))/4 := by
  let t := coordinate x
  have ht := coordinate_ne_zero x
  have hpow : t^m=t^(m-1)*t := by
    simpa only [sub_add_cancel,zpow_one] using (zpow_add₀ ht (m-1) 1)
  rw [factored,derivative_of_leading_power,hpow] at equation
  change ν*(t^(m-1)*((m:ℂᵣ)*v+t*δ v)) = -4*a*(t^(m-1)*t*v) at equation
  have balance : ν*((m:ℂᵣ)*v+t*δ v) = -4*a*t*v := by
    apply mul_left_cancel₀ (zpow_ne_zero (m-1) ht)
    linear_combination equation
  dsimp only
  change t*a = -(ν*((m:ℂᵣ)+t*δ v/v))/4
  field_simp [hv]
  linear_combination balance

private theorem quotient_log_value {x c : ℂ} {v : ℂᵣ} (m : ℤ)
    (hv : RadiusValue x v c) (hc : c≠0) :
    RadiusValue x ((m:ℂᵣ)+coordinate x*δ v/v) (m:ℂ) := by
  have mv : RadiusValue x (m:ℂᵣ) (m:ℂ) := by simpa only [map_intCast] using RadiusValue.const x (m:ℂ)
  obtain ⟨d,hd⟩ := hv.derivative
  simpa only [zero_mul,zero_div,add_zero] using mv.add (((coordinate_value x).mul hd).div hv hc)

theorem discriminant_ordinary_order {h k x : ℂ} {a b : ℂᵣ} (q : QuadraticRiccati h k a b)
    (hx0 : x≠0) (hx2 : x≠2) :
    finiteOrder b x = 0 ∨ finiteOrder b x = -2 := by
  obtain ⟨v,c,hc,hv,he⟩ := leading_at_finite b q.nonzero x
  let t := coordinate x
  let m := finiteOrder b x
  let f0 := (x-2)/x
  let w := -(radialFactor*((m:ℂᵣ)+t*δ v/v))/4
  have ht := coordinate_ne_zero x
  have ef : t*a=w := mean_times_coordinate (hv.ne_zero_of_value hc) he q.discriminant
  have hw : RadiusValue x w (-(f0*(m:ℂ))/4) :=
    ((factor_value hx0).mul (quotient_log_value m hv hc)).neg.div (four_value x) (by norm_num)
  have de := congrArg δ ef
  change δ (t*a) = δ w at de
  rw [rationalDerivative_mul,show δ t=1 from coordinate_derivative x,one_mul] at de
  have da : t^2*δ a = t*δ w-w := by linear_combination t*de-ef
  have eb : t^2*b=t^(m+2)*v := by
    rw [he,zpow_add₀ ht,zpow_ofNat]
    ring
  have scaled : radialFactor*(t*δ w-w)+w^2+t^(m+2)*v=t^2*parentTerm h k := calc
    _ = t^2*(D a+a^2+b) := by
      rw [← da,← ef,← eb,tortoiseDerivative]
      ring
    _ = _ := congrArg (fun c => t^2*c) q.mean
  obtain ⟨dw,hdw⟩ := hw.derivative
  have l := ((factor_value hx0).mul (((coordinate_value x).mul hdw).sub hw)).add (hw.pow 2)
  have r := ((coordinate_value x).pow 2).mul (parentTerm_value h k x hx0)
  have reg : RegularAt x (t^(m+2)*v) := by
    have eq : t^(m+2)*v = t^2*parentTerm h k - (radialFactor*(t*δ w-w)+w^2) := by linear_combination scaled
    exact ⟨_, eq ▸ r.sub l⟩
  have hge : 0 ≤ m+2 := nonnegative_power_of_regular reg hv hc rfl
  by_cases hz : m+2=0
  · exact Or.inr (by change m = -2; omega)
  have positive := (coordinate_zpow_positive x (show 0 < m+2 by omega)).mul hv
  have l' := l.add positive
  rw [scaled] at l'
  have value := l'.unique r
  have zero : f0^2*((m:ℂ)*((m:ℂ)+4))=0 := by
    change _ at value
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,zero_sub,add_zero] at value
    linear_combination 16*value
  have fne : f0≠0 := div_ne_zero (sub_ne_zero.mpr hx2) hx0
  have roots := (mul_eq_zero.mp zero).resolve_left (pow_ne_zero 2 fne)
  rcases mul_eq_zero.mp roots with h0 | hneg
  · exact Or.inl (by exact_mod_cast h0)
  · have h4 : (m:ℂ)=(-4:ℂ) := by linear_combination hneg
    have ne : m=(-4:ℤ) := by exact_mod_cast h4
    omega

theorem discriminant_horizon_order {h k : ℂ} {a b : ℂᵣ} (q : QuadraticRiccati h k a b)
    (hk : k≠0) (ki : k.re=0) :
    finiteOrder b 2 = 0 := by
  obtain ⟨v,c,hc,hv,he⟩ := leading_at_finite b q.nonzero 2
  let m := finiteOrder b 2
  let t := coordinate 2
  let w := (m:ℂᵣ)+t*δ v/v
  have hfa : radialFactor=t/R := by simp [radialFactor, t, coordinate_eq, map_ofNat]
  have ef : t*a = -(radialFactor*w)/4 := mean_times_coordinate (hv.ne_zero_of_value hc) he q.discriminant
  have aform : a = -(1/R*w)/4 := by
    apply mul_left_cancel₀ (coordinate_ne_zero 2)
    rw [ef,hfa]
    ring
  have wv := quotient_log_value m hv hc
  have iz := (RadiusValue.one 2).div (RadiusValue.radius 2) (by norm_num : (2:ℂ)≠0)
  have av : RadiusValue 2 a (-((1:ℂ)/2*(m:ℂ))/4) := by
    rw [aform]
    exact (iz.mul wv).neg.div (four_value 2) (by norm_num)
  obtain ⟨d,dd⟩ := av.derivative
  have dv : RadiusValue 2 (D a) 0 := by
    have f := factor_value (show (2:ℂ)≠0 by norm_num)
    have f0 : RadiusValue 2 radialFactor 0 := by simpa only [sub_self,zero_div] using f
    simpa only [tortoiseDerivative,zero_mul] using f0.mul dd
  let ac : ℂ := -((1:ℂ)/2*(m:ℂ))/4
  have kv : RadiusValue 2 (parentTerm h k) (k^2) := by
    simpa only [sub_self,zero_div,zero_mul,add_zero] using
      parentTerm_value h k 2 (by norm_num)
  have val : RadiusValue 2 b (k^2-ac^2) := by
    have eq : b=parentTerm h k-(D a+a^2) := by linear_combination q.mean
    rw [eq]
    simpa only [zero_add] using kv.sub (dv.add (av.pow 2))
  have ge := nonnegative_power_of_regular ⟨_,val⟩ hv hc he
  by_contra nz
  have zero := (coordinate_zpow_positive 2 (show 0<(m:ℤ) by omega)).mul hv
  change RadiusValue 2 (t^m*v) _ at zero
  rw [← he,zero_mul] at zero
  have hsq : k^2-ac^2=0 := val.unique zero
  have aci : ac.im=0 := by
    dsimp only [ac]
    simp [Complex.mul_im]
  have re := congrArg Complex.re (sub_eq_zero.mp hsq)
  simp only [pow_two,Complex.mul_re,ki,aci,zero_mul,sub_zero] at re
  have kimZero : k.im=0 := by nlinarith [sq_nonneg ac.re, sq_nonneg k.im]
  exact hk (Complex.ext (by simpa using ki) (by simpa using kimZero))

private theorem degree_at_infinity {b : ℂᵣ} {c : ℂ} (hb : b≠0)
    (value : RadiusValue 0 (reciprocalHom b) c) (hc : c≠0) :
    b.num.natDegree=b.denom.natDegree := by
  have nr : b.num.reverse.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero,coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hb)
  have dr : b.denom.reverse.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero,coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr b.denom_ne_zero
  have dd : b.denom.reverse≠0 := fun h => dr (by simp [h])
  have shape : reciprocalHom b = (coordinate 0)^((b.denom.natDegree:ℤ)-b.num.natDegree) *
      (ι b.num.reverse/ι b.denom.reverse) := by
    conv_lhs => rw [← RatFunc.num_div_denom b,map_div₀,reciprocalHom_polynomial,
      reciprocalHom_polynomial,Polynomial.aeval_def,Polynomial.aeval_def,polynomial_reciprocal,polynomial_reciprocal]
    rw [coordinate_zero,zpow_natCast_sub_natCast₀ RatFunc.X_ne_zero]
    field_simp [RatFunc.X_ne_zero,RatFunc.algebraMap_ne_zero dd]
  have ord := zero_power_of_nonzero_value value hc (RadiusValue.fraction _ _ dr) (div_ne_zero nr dr) shape
  omega

theorem discriminant_equal_degrees {h k : ℂ} {a b : ℂᵣ} (q : QuadraticRiccati h k a b) (hk : k≠0) :
    b.num.natDegree=b.denom.natDegree := by
  let av := reciprocalHom a
  let bv := reciprocalHom b
  let f := reciprocalFactor
  have bn : bv≠0 := (map_ne_zero reciprocalHom).mpr q.nonzero
  obtain ⟨v,c,hc,hv,he⟩ := leading_at_finite bv bn 0
  let m := finiteOrder bv 0
  have ed := congrArg reciprocalHom q.discriminant
  change reciprocalHom (D b) = reciprocalHom (-4*a*b) at ed
  simp only [reciprocal_tortoiseDerivative,map_mul,map_neg,map_ofNat] at ed
  change -R^2*f*δ bv = -4*av*bv at ed
  have eq := mean_times_coordinate (hv.ne_zero_of_value hc) he (by simpa only [coordinate_zero] using ed)
  let w := (m:ℂᵣ)+R*δ v/v
  have eo : R*av = -((-R^2*f)*w)/4 := by simpa only [coordinate_zero] using eq
  have aform : av= R*f*w/4 := by
    apply mul_left_cancel₀ RatFunc.X_ne_zero
    rw [eo]
    ring
  have wv : RadiusValue 0 w (m:ℂ) := by
    simpa only [coordinate_zero] using quotient_log_value m hv hc
  have va : RadiusValue 0 av 0 := by
    rw [aform]
    simpa only [zero_mul,zero_div] using
      (((RadiusValue.radius 0).mul reciprocalFactor_value).mul wv).div (four_value 0) (by norm_num)
  obtain ⟨d,da⟩ := va.derivative
  have ea := congrArg reciprocalHom q.mean
  change reciprocalHom (D a+a^2+b)=reciprocalHom (parentTerm h k) at ea
  simp only [map_add,map_pow,reciprocal_tortoiseDerivative,reciprocal_parentTerm] at ea
  rw [← map_pow Cᵣ k 2] at ea
  change -R^2*f*δ av+av^2+bv = Cᵣ (k^2)+f*(Cᵣ h*R^2-6*R^3) at ea
  have hB : bv=(Cᵣ (k^2)+f*(Cᵣ h*R^2-6*R^3))-((-R^2)*f*δ av+av^2) := by linear_combination ea
  have s : RadiusValue 0 (6:ℂᵣ) 6 := by simpa only [map_ofNat] using RadiusValue.const 0 6
  have r := RadiusValue.radius 0
  have right := (RadiusValue.const 0 (k^2)).add
    (reciprocalFactor_value.mul (((RadiusValue.const 0 h).mul (r.pow 2)).sub (s.mul (r.pow 3))))
  have lhs := ((((r.pow 2).neg.mul reciprocalFactor_value).mul da).add (va.pow 2))
  have value : RadiusValue 0 bv (k^2) := by
    rw [hB]
    simpa only [zero_pow (by decide : (2:ℕ)≠0),zero_pow (by decide : (3:ℕ)≠0),zero_mul,
      mul_zero,sub_zero,add_zero,neg_zero] using right.sub lhs
  exact degree_at_infinity q.nonzero value (pow_ne_zero 2 hk)

#print axioms discriminant_ordinary_order
#print axioms discriminant_horizon_order
#print axioms discriminant_equal_degrees

end

end SchwarzschildLaurent
