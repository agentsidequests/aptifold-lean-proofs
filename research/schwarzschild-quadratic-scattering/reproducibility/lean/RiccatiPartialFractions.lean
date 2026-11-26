import RiccatiInfinity

/-! Reconstruct a rational log derivative from its finite residues and its value
at reciprocal radius zero. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

theorem constant_of_everywhere_regular {v : ℂᵣ}
    (finite : ∀ a : ℂ, RegularAt a v) (infinity : RegularAt 0 (reciprocalHom v)) :
    ∃ c : ℂ, v = Cᵣ c := by
  have den (a : ℂ) : v.denom.eval a ≠ 0 := by
    obtain ⟨c,hc⟩ := finite a
    exact hc.denom_ne_zero
  have power := denominator_power v (fun a _ => den a)
  have d : v.denom.natDegree = 0 := by
    by_contra h
    have value := congrArg (eval 0) power
    simp only [eval_pow,eval_X,zero_pow h] at value
    exact den 0 value
  have den1 : v.denom=1 := by rw [power,d,pow_zero]
  have hz : v=ι v.num := by
    conv_lhs => rw [← RatFunc.num_div_denom v]
    rw [den1,map_one,div_one]
  by_cases hp : v.num=0
  · exact ⟨0,by rw [hz,hp,map_zero,map_zero]⟩
  rw [hz] at infinity
  have hn := radiusValue_of_reciprocal_polynomial v.num hp infinity
  refine ⟨v.num.coeff 0, hz.trans ?_⟩
  calc
    _ = ι (C (v.num.coeff 0)) := congrArg ι (eq_C_of_natDegree_eq_zero hn)
    _ = _ := by rw [RatFunc.algebraMap_C]

private def poleTerm (a c : ℂ) : ℂᵣ := Cᵣ c / coordinate a

private theorem pole_coordinate_value (a b c : ℂ) :
    RadiusValue a (coordinate a * poleTerm b c) (if a=b then c else 0) := by
  by_cases h : a=b
  · subst b
    simp only [poleTerm]
    rw [mul_div_cancel₀ _ (coordinate_ne_zero a)]
    exact RadiusValue.const a c
  have ht : RadiusValue a (coordinate b) (a-b) := by
    rw [coordinate_eq]
    exact (RadiusValue.radius a).sub (RadiusValue.const a b)
  simpa only [if_neg h,zero_mul,poleTerm] using
    (coordinate_value a).mul ((RadiusValue.const a c).div ht (sub_ne_zero.mpr h))

private theorem pole_term_reciprocal (a c : ℂ) :
    reciprocalHom (poleTerm a c) = Cᵣ c*R/(1-Cᵣ a*R) := by
  have lead : RadiusValue 0 (1-Cᵣ a*R) 1 := by
    simpa only [mul_zero,sub_zero] using
      (RadiusValue.one 0).sub ((RadiusValue.const 0 a).mul (RadiusValue.radius 0))
  have hlead := lead.ne_zero_of_value one_ne_zero
  have ht : R⁻¹-Cᵣ a ≠ 0 := by
    simpa only [map_sub,reciprocalHom_radius,reciprocalHom_constant] using
      (map_ne_zero reciprocalHom).mpr (shifted_radius_ne_zero a)
  simp only [poleTerm,coordinate_eq,map_div₀,map_sub,reciprocalHom_radius,reciprocalHom_constant]
  field_simp [RatFunc.X_ne_zero,ht,hlead]

private theorem pole_at_infinity (a c : ℂ) :
    RadiusValue 0 (reciprocalHom (poleTerm a c)) 0 ∧
      RadiusValue 0 (δ (reciprocalHom (poleTerm a c))) c := by
  have r := RadiusValue.radius 0
  have d := (RadiusValue.one 0).sub ((RadiusValue.const 0 a).mul r)
  have hd : RadiusValue 0 (1-Cᵣ a*R) 1 := by simpa only [mul_zero,sub_zero] using d
  rw [pole_term_reciprocal]
  constructor
  · simpa only [mul_zero,zero_div] using ((RadiusValue.const 0 c).mul r).div hd one_ne_zero
  · rw [rationalDerivative_div]
    have hn : δ (Cᵣ c*R)=Cᵣ c := by simp [rationalDerivative_mul]
    have hdn : δ (1-Cᵣ a*R) = -Cᵣ a := by simp [rationalDerivative_sub,rationalDerivative_mul]
    rw [hn,hdn]
    have v := (((RadiusValue.const 0 c).mul hd).sub
      (((RadiusValue.const 0 c).mul r).mul (RadiusValue.const 0 a).neg)).div
        (hd.pow 2) (by norm_num)
    simpa only [mul_one,mul_zero,zero_mul,sub_zero,one_pow,div_one] using v

theorem rationalDerivative_sum {I : Type*} (s : Finset I) (u : I → ℂᵣ) :
    δ (∑ a ∈ s, u a) = ∑ a ∈ s, δ (u a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,rationalDerivative_add,ih]

private theorem pole_sum_finite (s : Finset ℂ) (a : ℂ) :
    RadiusValue a (coordinate a * ∑ b ∈ s, poleTerm b 1) (if a∈s then 1 else 0) := by
  classical
  rw [Finset.mul_sum]
  have val := RadiusValue.sum s _ (fun b => if a=b then 1 else 0)
    (fun b _ => pole_coordinate_value a b 1)
  suffices sum : (∑ b ∈ s, if a=b then (1:ℂ) else 0) = if a∈s then 1 else 0 by
    rwa [sum] at val
  simp only [eq_comm (a := a)]
  simp

private def residueSum (r0 r2 : ℂ) (s : Finset ℂ) : ℂᵣ :=
  poleTerm 0 r0 + poleTerm 2 r2 + ∑ a ∈ s, poleTerm a 1

private theorem residueSum_finite (r0 r2 : ℂ) (s : Finset ℂ) (a : ℂ) :
    RadiusValue a (coordinate a * residueSum r0 r2 s)
      ((if a=0 then r0 else 0)+(if a=2 then r2 else 0)+(if a∈s then 1 else 0)) := by
  classical
  unfold residueSum
  rw [mul_add,mul_add]
  exact ((pole_coordinate_value a 0 r0).add (pole_coordinate_value a 2 r2)).add
    (pole_sum_finite s a)

private theorem residueSum_infinity (r0 r2 : ℂ) (s : Finset ℂ) :
    RadiusValue 0 (reciprocalHom (residueSum r0 r2 s)) 0 ∧
    RadiusValue 0 (δ (reciprocalHom (residueSum r0 r2 s))) (r0+r2+s.card) := by
  simp only [residueSum,map_add,map_sum,rationalDerivative_add,rationalDerivative_sum]
  have h0 := pole_at_infinity 0 r0
  have h2 := pole_at_infinity 2 r2
  have first := (h0.1.add h2.1).add (RadiusValue.sum s _ (fun _ => 0) (fun a _ => (pole_at_infinity a 1).1))
  have second := (h0.2.add h2.2).add (RadiusValue.sum s _ (fun _ => 1) (fun a _ => (pole_at_infinity a 1).2))
  exact ⟨by simpa only [zero_add,Finset.sum_const_zero] using first, by simpa using second⟩

/-- The sum of the finite residues equals the coefficient of 1/r at infinity. -/
theorem log_partial_fractions {h k : ℂ} {z : ℂᵣ} (eq : LogDerivativeEquation h k z) (hk : k ≠ 0) :
    ∃ (c r0 r2 : ℂ) (s : Finset ℂ), c^2=k^2 ∧ (r0 = -1 ∨ r0=3) ∧
      (r2=2*k ∨ r2=-(2*k)) ∧ (0:ℂ)∉s ∧ (2:ℂ)∉s ∧
      z=Cᵣ c+residueSum r0 r2 s ∧ r0+r2+s.card=2*c := by
  classical
  obtain ⟨c,hc,hsq,hslope⟩ := infinity_log_coefficients eq hk
  obtain ⟨r0,h0,h0'⟩ := origin_log_residue eq
  obtain ⟨r2,h2,h2'⟩ := horizon_log_residue eq
  let s := z.denom.roots.toFinset.filter (fun b : ℂ => b≠0 ∧ b≠2)
  have member (a : ℂ) : a ∈ s ↔ z.denom.eval a=0 ∧ a≠0 ∧ a≠2 := by
    simp only [s,Finset.mem_filter,Multiset.mem_toFinset,mem_roots z.denom_ne_zero,IsRoot]
  have no0 : (0:ℂ)∉s := fun h => ((member 0).mp h).2.1 rfl
  have no2 : (2:ℂ)∉s := fun h => ((member 2).mp h).2.2 rfl
  let q := residueSum r0 r2 s
  let v := z-q
  have fq (a : ℂ) : RadiusValue a (coordinate a*z)
      ((if a=0 then r0 else 0)+(if a=2 then r2 else 0)+(if a∈s then 1 else 0)) := by
    by_cases z0 : a=0
    · subst a
      simpa only [if_true,show (0:ℂ)≠2 by norm_num,if_false,add_zero,no0] using h0
    by_cases z2 : a=2
    · subst a
      simpa only [if_true,show (2:ℂ)≠0 by norm_num,if_false,zero_add,add_zero,no2] using h2
    by_cases p : a∈s
    · obtain ⟨b,hb,ho⟩ := ordinary_log_residue z0 z2 eq
      rcases ho with hb0 | hb1
      · rw [hb0] at hb
        obtain ⟨u,hu⟩ := regular_of_coordinate_mul_zero hb
        exact False.elim (hu.denom_ne_zero ((member a).mp p).1)
      · rw [hb1] at hb
        simpa only [if_neg z0,if_neg z2,if_pos p,zero_add] using hb
    · have nz : z.denom.eval a ≠ 0 := fun h => p ((member a).mpr ⟨h,z0,z2⟩)
      obtain ⟨b,hb⟩ := regular_of_denom_ne_zero nz
      simpa only [if_neg z0,if_neg z2,if_neg p,zero_add,zero_mul] using (coordinate_value a).mul hb
  have fixFinite (a : ℂ) : RegularAt a v := by
    apply regular_of_coordinate_mul_zero
    unfold v
    rw [mul_sub]
    simpa only [sub_self] using (fq a).sub (residueSum_finite r0 r2 s a)
  have ⟨q0,q1⟩ := residueSum_infinity r0 r2 s
  have fixInfinity : RadiusValue 0 (reciprocalHom v) c := by
    dsimp only [v]
    rw [map_sub]
    simpa only [sub_zero] using hc.sub q0
  obtain ⟨v0,ev⟩ := constant_of_everywhere_regular fixFinite ⟨_,fixInfinity⟩
  have same : c = v0 := by
    rw [ev,reciprocalHom_constant] at fixInfinity
    exact fixInfinity.unique (RadiusValue.const 0 v0)
  have eqz : z=Cᵣ c+q := by
    unfold v at ev
    rw [same]
    linear_combination ev
  have derivative : δ (reciprocalHom z) = δ (reciprocalHom q) := by
    rw [eqz,map_add,reciprocalHom_constant,rationalDerivative_add,rationalDerivative_constant,zero_add]
  rw [derivative] at hslope
  exact ⟨c,r0,r2,s,hsq,h0',h2',no0,no2,eqz,q1.unique hslope⟩

/-- For a purely imaginary nonzero k the finite residues force exactly one
ordinary pole and fix the horizon sign to the sign at infinity. -/
theorem log_candidate {h k : ℂ} {z : ℂᵣ} (eq : LogDerivativeEquation h k z) (hk : k ≠ 0) (hre : k.re=0) :
    ∃ (c b : ℂ), c^2=k^2 ∧ c.re=0 ∧ b≠0 ∧ b≠2 ∧
      z=Cᵣ c + Cᵣ (2*c)/coordinate 2 - 1/R + 1/coordinate b := by
  obtain ⟨c,r0,r2,s,hc,hr0,hr2,no0,no2,hz,hsum⟩ := log_partial_fractions eq hk
  have fac : (c-k)*(c+k)=0 := by linear_combination hc
  have cReal : c.re=0 := by
    rcases mul_eq_zero.mp fac with hp | hn
    · rw [sub_eq_zero.mp hp,hre]
    · have ee : c=-k := by linear_combination hn
      rw [ee,Complex.neg_re,hre,neg_zero]
  have hi2 : (2:ℂ).im=0 := by norm_num
  have kr : (2*k).re=0 := by simp [Complex.mul_re,hre,hi2]
  have cr : (2*c).re=0 := by simp [Complex.mul_re,cReal,hi2]
  have r2Real : r2.re=0 := by
    rcases hr2 with hpos | hneg
    · rw [hpos,kr]
    · rw [hneg,Complex.neg_re,kr,neg_zero]
  have realEq := congrArg Complex.re hsum
  simp only [Complex.add_re,Complex.natCast_re,r2Real,add_zero,cr] at realEq
  have orig : r0 = -1 := by
    rcases hr0 with e | e
    · exact e
    · rw [e,show (3:ℂ).re=3 by norm_num] at realEq
      have hn : (0:ℝ)≤s.card := Nat.cast_nonneg _
      linarith
  have single : s.card=1 := by
    rw [orig,Complex.neg_re,Complex.one_re] at realEq
    exact_mod_cast (by linarith : (s.card:ℝ)=1)
  obtain ⟨b,sb⟩ := Finset.card_eq_one.mp single
  have b0 : b≠0 := by intro e; subst b; exact no0 (by simp [sb])
  have b2 : b≠2 := by intro e; subst b; exact no2 (by simp [sb])
  have hsign : r2=2*c := by rw [orig,single,Nat.cast_one] at hsum; linear_combination hsum
  refine ⟨c,b,hc,cReal,b0,b2,?_⟩
  rw [hz,orig,hsign,sb]
  simp only [residueSum,poleTerm,Finset.sum_singleton,coordinate_zero,map_neg,map_one]
  ring

#print axioms constant_of_everywhere_regular
#print axioms log_partial_fractions
#print axioms log_candidate

end

end SchwarzschildLaurent
