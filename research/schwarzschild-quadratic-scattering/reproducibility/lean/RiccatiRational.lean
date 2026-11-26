import RiccatiPartialFractions

/-! Exclude the one-pole form forced on a rational Riccati solution. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative
local notation "D" => tortoiseDerivative

private theorem tortoise_quotient (x y : ℂᵣ) :
    D (x/y) = (D x*y-x*D y)/y^2 := by
  unfold tortoiseDerivative
  rw [rationalDerivative_div,← mul_div_assoc]
  congr 1
  ring

private theorem candidate_equations {h k : ℂ} {u : ℂᵣ} (eq : RationalRiccati h k u)
    {c b : ℂ} (hc : c^2=k^2)
    (form : u/radialFactor=Cᵣ c+Cᵣ (2*c)/coordinate 2-1/R+1/coordinate b) :
    2*c*b=h ∧ b*(h-2)+6=0 := by
  let w := 1-Cᵣ b/R
  have wr : w=(R-Cᵣ b)/R := by
    dsimp only [w]
    field_simp [RatFunc.X_ne_zero]
  have wn : w≠0 := by rw [wr]; exact div_ne_zero (shifted_radius_ne_zero b) RatFunc.X_ne_zero
  have dw : D w = radialFactor*(Cᵣ b/R^2) := by
    simp only [w,tortoiseDerivative,rationalDerivative_sub,rationalDerivative_div,
      rationalDerivative_one,rationalDerivative_constant,rationalDerivative_radius,zero_mul,mul_one,zero_sub]
    ring
  have df : δ radialFactor = 2/R^2 := by
    have htwo : δ (2:ℂᵣ) = 0 := by simpa only [map_ofNat] using rationalDerivative_constant 2
    simp only [radialFactor,rationalDerivative_div,rationalDerivative_sub,rationalDerivative_radius,
      htwo,sub_zero,one_mul,mul_one]
    ring
  have d2w : D (D w) = radialFactor*(Cᵣ b*(6/R^4-2/R^3)) := by
    rw [dw]
    simp only [tortoiseDerivative,rationalDerivative_mul,df,rationalDerivative_div,
      rationalDerivative_constant,rationalDerivative_pow,rationalDerivative_radius,
      zero_mul,mul_one,zero_sub]
    simp only [radialFactor]
    norm_num
    field_simp [RatFunc.X_ne_zero] <;> ring_nf <;> simp
  have uw : u = Cᵣ c+(D w)/w := calc
    _ = radialFactor*(u/radialFactor) := (mul_div_cancel₀ _ radialFactor_ne_zero).symm
    _ = _ := by
      rw [form,dw,wr]
      simp only [coordinate_eq,map_mul,map_ofNat,radialFactor]
      field_simp [RatFunc.X_ne_zero,radius_minus_two_ne_zero,shifted_radius_ne_zero b]
      ring
  have expanded : D (Cᵣ c+D w/w)+(Cᵣ c+D w/w)^2 =
      Cᵣ (c^2)+(D (D w)+2*Cᵣ c*D w)/w := by
    simp only [tortoise_add,tortoise_const,zero_add,tortoise_quotient,map_pow]
    field_simp [wn]
    ring
  unfold RationalRiccati at eq
  rw [uw,expanded,hc,parentTerm] at eq
  have wave : D (D w)+2*Cᵣ c*D w = oddPotential h*w :=
    (div_eq_iff wn).mp (add_left_cancel eq)
  have reduced : Cᵣ b*(6/R^4-2/R^3)+2*Cᵣ c*(Cᵣ b/R^2) = (Cᵣ h/R^2-6/R^3)*w := by
    rw [d2w,dw,oddPotential] at wave
    apply mul_left_cancel₀ radialFactor_ne_zero
    linear_combination wave
  have cleared : R^4*(Cᵣ b*(6/R^4-2/R^3)+2*Cᵣ c*(Cᵣ b/R^2)-(Cᵣ h/R^2-6/R^3)*w) =
      R*((2*Cᵣ c*Cᵣ b-Cᵣ h)*R+Cᵣ b*(Cᵣ h-2)+6) := by
    dsimp only [w]
    field_simp [RatFunc.X_ne_zero]
    ring
  rw [sub_eq_zero.mpr reduced,mul_zero] at cleared
  have coef := (mul_eq_zero.mp cleared.symm).resolve_left RatFunc.X_ne_zero
  have p : (C (2*c*b-h)*X+C (b*(h-2)+6) : ℂ[X])=0 := by
    apply RatFunc.algebraMap_injective ℂ
    simpa only [map_zero,map_mul,map_sub,map_add,map_ofNat,RatFunc.algebraMap_C,RatFunc.algebraMap_X,add_assoc] using coef
  have q0 := congrArg (eval 0) p
  have q1 := congrArg (eval 1) p
  simp only [eval_add,eval_mul,eval_X,eval_C,eval_zero,mul_zero,zero_add,mul_one] at q0 q1
  exact ⟨sub_eq_zero.mp (by simpa only [q0,add_zero] using q1),q0⟩

/-- No rational logarithmic derivative at a nonzero, purely imaginary
frequency parameter and a physical angular label. -/
theorem rational_riccati_no_solution (n : ℕ) (hn : 2 ≤ n) (k : ℂ) (hk : k≠0) (ki : k.re=0) :
    ¬ ∃ u, RationalRiccati ((n:ℂ)*((n:ℂ)+1)) k u := by
  rintro ⟨u,eq⟩
  let h : ℂ := (n:ℂ)*((n:ℂ)+1)
  have eq' : RationalRiccati h k u := eq
  obtain ⟨c,b,hc,cReal,_,_,shape⟩ := log_candidate (logDerivativeEquation_of_riccati eq') hk ki
  obtain ⟨h1,h2⟩ := candidate_equations eq' hc shape
  have obstruction : h*(h-2) = -12*c := by
    linear_combination -(h-2)*h1+2*c*h2
  have him : h.im=0 := by simp [h,Complex.mul_im]
  have large : 6≤h.re := by
    simp only [h,Complex.mul_re,Complex.natCast_re,Complex.add_re,Complex.one_re,
      Complex.natCast_im,zero_mul,sub_zero]
    have real : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
    nlinarith
  have real := congrArg Complex.re obstruction
  have rhs : (-12*c).re=0 := by simp [Complex.mul_re,cReal]
  rw [rhs,Complex.mul_re,him,zero_mul,sub_zero,Complex.sub_re,show (2:ℂ).re=2 by norm_num] at real
  nlinarith

/-- The algebraically special ell=2 mode is a rational solution at the real
frequency parameter k=-2. It tests the boundary of the frequency hypothesis. -/
theorem algebraically_special_rational_control :
    RationalRiccati 6 (-2)
      (Cᵣ (-2)-Cᵣ 3*(R-Cᵣ 2)/(R^2*(Cᵣ 2*R+Cᵣ 3))) := by
  have denom : Cᵣ 2*R+Cᵣ 3 ≠ 0 := by
    intro hz
    have q : (C (2:ℂ)*X+C 3 : ℂ[X])=0 := by
      apply RatFunc.algebraMap_injective ℂ
      simpa only [map_add,map_mul,map_zero,RatFunc.algebraMap_C,RatFunc.algebraMap_X] using hz
    have e := congrArg (eval 0) q
    norm_num at e
  let Q := Cᵣ 2*R+Cᵣ 3
  have qn : Q≠0 := denom
  have qd : δ Q = Cᵣ 2 := by
    simp only [Q,rationalDerivative_add,rationalDerivative_mul,rationalDerivative_constant,
      rationalDerivative_radius,zero_mul,mul_one,zero_add,add_zero]
  have kc : Cᵣ ((-2:ℂ)^2) = 4 := by rw [map_pow,map_neg,map_ofNat]; norm_num
  change RationalRiccati 6 (-2) (Cᵣ (-2)-Cᵣ 3*(R-Cᵣ 2)/(R^2*Q))
  unfold RationalRiccati tortoiseDerivative parentTerm oddPotential
  simp only [rationalDerivative_sub,rationalDerivative_mul,rationalDerivative_add,rationalDerivative_pow,
    rationalDerivative_div,rationalDerivative_constant,rationalDerivative_radius,qd,kc]
  simp only [radialFactor,map_neg,map_ofNat]
  field_simp [RatFunc.X_ne_zero,qn]
  dsimp only [Q]
  simp only [map_ofNat]
  ring

#print axioms algebraically_special_rational_control

#print axioms rational_riccati_no_solution

end

end SchwarzschildLaurent
