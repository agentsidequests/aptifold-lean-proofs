import RiccatiFinite

/-! The first two coefficients of the log derivative at reciprocal radius zero. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

def reciprocalFactor : ℂᵣ := 1-2*R

theorem reciprocal_radialFactor (u : ℂᵣ) : reciprocalHom (radialFactor*u) =
    reciprocalFactor*reciprocalHom u := by
  simp only [radialFactor, reciprocalFactor, map_mul, map_div₀, map_sub, map_ofNat, reciprocalHom_radius]
  field_simp [RatFunc.X_ne_zero]

theorem reciprocal_derivative_map (u : ℂᵣ) :
    reciprocalHom (δ u) = -R^2*δ (reciprocalHom u) := by
  rw [derivative_reciprocal]
  field_simp [RatFunc.X_ne_zero]

theorem reciprocal_tortoiseDerivative (u : ℂᵣ) :
    reciprocalHom (tortoiseDerivative u) = -R^2*reciprocalFactor*δ (reciprocalHom u) := by
  rw [tortoiseDerivative, reciprocal_radialFactor, reciprocal_derivative_map]
  ring

theorem reciprocal_parentTerm (h k : ℂ) :
    reciprocalHom (parentTerm h k) = Cᵣ (k^2)+reciprocalFactor*(Cᵣ h*R^2-6*R^3) := by
  simp only [parentTerm, oddPotential, map_add, reciprocalHom_constant, reciprocal_radialFactor,
    map_sub, map_div₀, map_pow, map_ofNat, reciprocalHom_radius]
  field_simp [RatFunc.X_ne_zero]

def ReciprocalLogEquation (h k : ℂ) (v : ℂᵣ) : Prop :=
  reciprocalFactor^2*(-R^2*δ v+v^2) + 2*R^2*reciprocalFactor*v =
    Cᵣ (k^2) + reciprocalFactor*(Cᵣ h*R^2-6*R^3)

theorem reciprocal_log_eq {h k : ℂ} {z : ℂᵣ} (e : LogDerivativeEquation h k z) :
    ReciprocalLogEquation h k (reciprocalHom z) := by
  have product : reciprocalHom radiusProduct = reciprocalFactor/R^2 := by
    simp only [radiusProduct, reciprocalFactor, map_mul, map_sub, map_ofNat, reciprocalHom_radius]
    field_simp [RatFunc.X_ne_zero]
  have rhs : R^4*reciprocalHom (ι (jetA h k)) =
      Cᵣ (k^2)+reciprocalFactor*(Cᵣ h*R^2-6*R^3) := by
    simp only [jetA, map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      reciprocalHom_radius, reciprocalHom_constant, reciprocalFactor, map_ofNat]
    field_simp [RatFunc.X_ne_zero]
    ring
  unfold LogDerivativeEquation at e
  have transformed := congrArg reciprocalHom e
  change reciprocalHom _ = reciprocalHom _ at transformed
  simp only [map_add,map_mul,map_pow,map_ofNat,product,reciprocal_derivative_map] at transformed
  unfold ReciprocalLogEquation
  rw [← rhs, ← transformed]
  field_simp [RatFunc.X_ne_zero]

theorem reciprocalFactor_value : RadiusValue 0 reciprocalFactor 1 := by
  have ht : RadiusValue 0 (Cᵣ (2:ℂ)) 2 := RadiusValue.const 0 2
  have h := (RadiusValue.one 0).sub (ht.mul (RadiusValue.radius 0))
  simpa [reciprocalFactor, map_ofNat] using h

private theorem reciprocal_potential_value (h k : ℂ) :
    RadiusValue 0 (Cᵣ (k^2)+reciprocalFactor*(Cᵣ h*R^2-6*R^3)) (k^2) := by
  have h6 : RadiusValue 0 (6:ℂᵣ) 6 := by simpa only [map_ofNat] using RadiusValue.const 0 6
  have r := RadiusValue.radius 0
  simpa only [zero_pow (by decide : (2:ℕ) ≠ 0), zero_pow (by decide : (3:ℕ) ≠ 0),
    mul_zero, sub_zero, add_zero] using (RadiusValue.const 0 (k^2)).add
    (reciprocalFactor_value.mul (((RadiusValue.const 0 h).mul (r.pow 2)).sub (h6.mul (r.pow 3))))

private theorem reciprocal_log_rescale {h k : ℂ} {v w : ℂᵣ} {m : ℤ}
    (eq : ReciprocalLogEquation h k v) (hv : v=R^m*w) :
    reciprocalFactor^2*(-R^(1-m)*((m:ℂᵣ)*w+R*δ w)+w^2) +
      2*reciprocalFactor*R^(2-m)*w =
    R^(-2*m)*(Cᵣ (k^2)+reciprocalFactor*(Cᵣ h*R^2-6*R^3)) := by
  let g := reciprocalFactor
  let t := (m:ℂᵣ)*w+R*δ w
  have d : δ (R^m*w) = R^(m-1)*t := by
    simpa only [coordinate_zero] using derivative_of_leading_power 0 m w
  unfold ReciprocalLogEquation at eq
  rw [hv,d] at eq
  calc
    _ = R^(-2*m)*(g^2*(-R^2*(R^(m-1)*t)+(R^m*w)^2)+2*R^2*g*(R^m*w)) := by
      symm
      calc
        _ = -(R^(-2*m)*R^(2:ℤ)*R^(m-1))*g^2*t +
            (R^(-2*m)*R^m*R^m)*g^2*w^2 + 2*g*(R^(-2*m)*R^(2:ℤ)*R^m)*w := by
          simp only [zpow_ofNat]
          ring
        _ = _ := by
          simp only [← zpow_add₀ (RatFunc.X_ne_zero (K := ℂ))]
          rw [show -2*m+2+(m-1)=1-m by omega, show -2*m+m+m=0 by omega,
            show -2*m+2+m=2-m by omega,zpow_zero]
          ring
    _ = _ := congrArg (fun x => R^(-2*m)*x) eq

private theorem reciprocal_log_regular {h k : ℂ} {v : ℂᵣ} (eq : ReciprocalLogEquation h k v) :
    RegularAt 0 v := by
  by_cases hv : v=0
  · exact ⟨0, hv ▸ RadiusValue.zero 0⟩
  obtain ⟨w,c,hc,hw,he⟩ := leading_at_finite v hv 0
  let m := finiteOrder v 0
  rw [coordinate_zero] at he
  have hm : 0 ≤ m := by
    by_contra! hm
    have er := reciprocal_log_rescale eq he
    obtain ⟨d,hd⟩ := hw.derivative
    have hmval : RadiusValue 0 (m:ℂᵣ) (m:ℂ) := by
      simpa only [map_intCast] using RadiusValue.const 0 (m:ℂ)
    have hz (n : ℤ) (hn : 0 < n) : RadiusValue 0 (R^n) 0 := by
      simpa only [coordinate_zero] using coordinate_zpow_positive 0 hn
    have first := (hz (1-m) (by omega)).neg.mul ((hmval.mul hw).add ((RadiusValue.radius 0).mul hd))
    have ht : RadiusValue 0 (2:ℂᵣ) 2 := by simpa only [map_ofNat] using RadiusValue.const 0 2
    have second := ((ht.mul reciprocalFactor_value).mul (hz (2-m) (by omega))).mul hw
    have rhs := (hz (-2*m) (by omega)).mul (reciprocal_potential_value h k)
    have lhs := ((reciprocalFactor_value.pow 2).mul (first.add (hw.pow 2))).add second
    rw [er] at lhs
    have e := lhs.unique rhs
    simp only [one_pow,neg_zero,zero_mul,zero_add,one_mul,mul_one,mul_zero,add_zero] at e
    exact (pow_ne_zero 2 hc) e
  have tv : RadiusValue 0 (R^m) (if m=0 then 1 else 0) := by
    simpa only [coordinate_zero] using coordinate_zpow_value 0 m hm
  rw [he]
  exact ⟨_, tv.mul hw⟩

private theorem reciprocalFactor_derivative : δ reciprocalFactor = (-2:ℂᵣ) := by
  have htwo : δ (2:ℂᵣ) = 0 := by simpa only [map_ofNat] using rationalDerivative_constant 2
  simp [reciprocalFactor, rationalDerivative_sub, rationalDerivative_mul, htwo]

/-- At infinity z has constant part ±k and the next coefficient is twice
that constant part. -/
theorem infinity_log_coefficients {h k : ℂ} {z : ℂᵣ} (eq : LogDerivativeEquation h k z) (hk : k ≠ 0) :
    ∃ c, RadiusValue 0 (reciprocalHom z) c ∧ c^2=k^2 ∧
      RadiusValue 0 (δ (reciprocalHom z)) (2*c) := by
  let v := reciprocalHom z
  let g := reciprocalFactor
  have e : ReciprocalLogEquation h k v := reciprocal_log_eq eq
  obtain ⟨c,hv⟩ := reciprocal_log_regular e
  obtain ⟨d,hd⟩ := hv.derivative
  let w := g^2*δ v-2*g*v+g*(Cᵣ h-6*R)
  unfold ReciprocalLogEquation at e
  have rewrite : (g*v)^2 = Cᵣ (k^2)+R^2*w := by
    dsimp only [g,w]
    linear_combination e
  have hn (n : ℕ) : RadiusValue 0 (n:ℂᵣ) (n:ℂ) := by
    simpa only [map_natCast] using RadiusValue.const 0 (n:ℂ)
  have rg := reciprocalFactor_value
  have rv := RadiusValue.radius 0
  have rwv := (((rg.pow 2).mul hd).sub (((hn 2).mul rg).mul hv)).add
    (rg.mul ((RadiusValue.const 0 h).sub ((hn 6).mul rv)))
  change RadiusValue 0 w _ at rwv
  have sq := (rg.mul hv).pow 2
  change RadiusValue 0 ((g*v)^2) _ at sq
  rw [rewrite] at sq
  have c2 : c^2 = k^2 := by
    simpa using sq.unique ((RadiusValue.const 0 (k^2)).add ((rv.pow 2).mul rwv))
  have hc : c ≠ 0 := by
    intro c0
    exact (pow_ne_zero 2 hk) (by simpa [c0] using c2.symm)
  have deriv_right := congrArg δ rewrite
  change δ ((g*v)^2) = δ (Cᵣ (k^2)+R^2*w) at deriv_right
  have deriv_left : δ ((g*v)^2) = 2*(g*v)*((-2)*v+g*δ v) := by
    simp only [rationalDerivative_pow,rationalDerivative_mul,show δ g=(-2:ℂᵣ) from reciprocalFactor_derivative]
    norm_num
  rw [deriv_left,rationalDerivative_add,rationalDerivative_constant,zero_add,rationalDerivative_mul,
    rationalDerivative_pow,rationalDerivative_radius] at deriv_right
  have da := (((hn 2).mul (rg.mul hv)).mul
    (((hn 2).neg.mul hv).add (rg.mul hd)))
  change RadiusValue 0 (2*(g*v)*((-2)*v+g*δ v)) _ at da
  rw [deriv_right] at da
  obtain ⟨dw,hw⟩ := rwv.derivative
  have db := ((((hn 2).mul (rv.pow (2-1))).mul (RadiusValue.one 0)).mul rwv).add
    ((rv.pow 2).mul hw)
  have values := da.unique db
  have de : d=2*c := by
    have h0 : 2*c*(d-2*c)=0 := by
      norm_num [-mul_eq_zero] at values
      linear_combination values
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero (by norm_num) hc))
  exact ⟨c,hv,c2,de ▸ hd⟩

#print axioms reciprocal_log_eq
#print axioms infinity_log_coefficients

end

end SchwarzschildLaurent
