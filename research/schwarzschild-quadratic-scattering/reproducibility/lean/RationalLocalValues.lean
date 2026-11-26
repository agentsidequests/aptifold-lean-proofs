import LaurentEmbedding

/-! Values and leading powers of complex rational functions at a finite point. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

/-- A rational function has value c at a if it has a fraction with a denominator
that is nonzero there and whose evaluation is c. -/
def RadiusValue (a : ℂ) (u : ℂᵣ) (c : ℂ) : Prop :=
  ∃ p q : ℂ[X], q.eval a ≠ 0 ∧ u = ι p / ι q ∧ c = p.eval a / q.eval a

def RegularAt (a : ℂ) (u : ℂᵣ) : Prop := ∃ c, RadiusValue a u c

private theorem poly_ne_zero {a : ℂ} {q : ℂ[X]} (h : q.eval a ≠ 0) : q ≠ 0 := by
  intro hz
  exact h (by simp [hz])

private theorem poly_image_ne_zero {a : ℂ} {q : ℂ[X]} (h : q.eval a ≠ 0) : ι q ≠ 0 :=
  RatFunc.algebraMap_ne_zero (poly_ne_zero h)

namespace RadiusValue

variable {a c d : ℂ} {u v : ℂᵣ}

theorem fraction (p q : ℂ[X]) (hq : q.eval a ≠ 0) :
    RadiusValue a (ι p / ι q) (p.eval a / q.eval a) :=
  ⟨p,q,hq,rfl,rfl⟩

theorem polynomial (a : ℂ) (p : ℂ[X]) : RadiusValue a (ι p) (p.eval a) := by
  simpa using fraction (a := a) p 1 (by simp)

theorem const (a c : ℂ) : RadiusValue a (Cᵣ c) c := by
  simpa using polynomial a (C c)

theorem zero (a : ℂ) : RadiusValue a 0 0 := by simpa using const a 0

theorem one (a : ℂ) : RadiusValue a 1 1 := by simpa using const a 1

theorem radius (a : ℂ) : RadiusValue a R a := by simpa using polynomial a (X : ℂ[X])

theorem unique (hu : RadiusValue a u c) (hv : RadiusValue a u d) : c = d := by
  obtain ⟨p,q,hq,hu,rfl⟩ := hu
  obtain ⟨r,s,hs,hv,rfl⟩ := hv
  have e : p*s = r*q := RatFunc.algebraMap_injective ℂ <| by
    simpa only [map_mul] using
      (div_eq_div_iff (poly_image_ne_zero hq) (poly_image_ne_zero hs)).mp (hu.symm.trans hv)
  exact (div_eq_div_iff hq hs).mpr (by simpa only [eval_mul] using congrArg (eval a) e)

theorem ne_zero_of_value (hu : RadiusValue a u c) (hc : c ≠ 0) : u ≠ 0 :=
  fun e => hc ((e ▸ hu).unique (zero a))

theorem add (hu : RadiusValue a u c) (hv : RadiusValue a v d) : RadiusValue a (u+v) (c+d) := by
  obtain ⟨p,q,hq,rfl,rfl⟩ := hu
  obtain ⟨r,s,hs,rfl,rfl⟩ := hv
  refine ⟨p*s+r*q,q*s,by simp [hq,hs],?_,?_⟩
  · simp only [map_add, map_mul]
    field_simp [poly_image_ne_zero hq, poly_image_ne_zero hs]
  · simp only [eval_add, eval_mul]
    field_simp [hq, hs]

theorem neg (hu : RadiusValue a u c) : RadiusValue a (-u) (-c) := by
  obtain ⟨p,q,hq,rfl,rfl⟩ := hu
  refine ⟨-p,q,hq,?_,?_⟩
  · simp only [map_neg, div_eq_mul_inv, neg_mul]
  · rw [eval_neg, neg_div]

theorem sub (hu : RadiusValue a u c) (hv : RadiusValue a v d) : RadiusValue a (u-v) (c-d) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

theorem mul (hu : RadiusValue a u c) (hv : RadiusValue a v d) : RadiusValue a (u*v) (c*d) := by
  obtain ⟨p,q,hq,rfl,rfl⟩ := hu
  obtain ⟨r,s,hs,rfl,rfl⟩ := hv
  exact ⟨p*r,q*s,by simp [hq,hs],by simp [div_mul_div_comm],by simp [div_mul_div_comm]⟩

theorem inv (hu : RadiusValue a u c) (hc : c ≠ 0) : RadiusValue a u⁻¹ c⁻¹ := by
  obtain ⟨p,q,hq,rfl,rfl⟩ := hu
  refine ⟨q,p,(div_ne_zero_iff.mp hc).1,?_,?_⟩ <;> rw [inv_div]

theorem div (hu : RadiusValue a u c) (hv : RadiusValue a v d) (hd : d ≠ 0) :
    RadiusValue a (u/v) (c/d) := by simpa only [div_eq_mul_inv] using hu.mul (hv.inv hd)

theorem pow (hu : RadiusValue a u c) (m : ℕ) : RadiusValue a (u^m) (c^m) := by
  induction m with
  | zero => simp [one]
  | succ m ih => simpa only [pow_succ] using ih.mul hu

theorem sum {I : Type*} (s : Finset I) (u : I → ℂᵣ) (c : I → ℂ)
    (hv : ∀ i ∈ s, RadiusValue a (u i) (c i)) :
    RadiusValue a (∑ i ∈ s, u i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (hv i (Finset.mem_insert_self ..)).add (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

theorem derivative (hu : RadiusValue a u c) : RegularAt a (δ u) := by
  obtain ⟨p,q,hq,rfl,_⟩ := hu
  rw [rationalDerivative_fraction p q (poly_ne_zero hq)]
  let n := p.derivative*q-p*q.derivative
  refine ⟨n.eval a / (q^2).eval a, n, q^2, by simp [hq], ?_, rfl⟩
  exact (congrArg (fun v : ℂᵣ => ι n / v) (map_pow ι q 2)).symm

theorem denom_ne_zero (hu : RadiusValue a u c) : u.denom.eval a ≠ 0 := by
  obtain ⟨p,q,hq,he,_⟩ := hu
  have cross : u.num*q = p*u.denom := RatFunc.algebraMap_injective ℂ <| by
    simpa only [map_mul] using (div_eq_div_iff (RatFunc.algebraMap_ne_zero u.denom_ne_zero)
      (poly_image_ne_zero hq)).mp ((RatFunc.num_div_denom u).trans he)
  intro hz
  have ev := congrArg (eval a) cross
  simp only [eval_mul, hz, mul_zero] at ev
  have hn := (mul_eq_zero.mp ev).resolve_right hq
  obtain ⟨x,y,e⟩ := u.isCoprime_num_denom
  have check := congrArg (eval a) e
  simp [hn,hz] at check

end RadiusValue

theorem regular_of_denom_ne_zero {a : ℂ} {u : ℂᵣ} (h : u.denom.eval a ≠ 0) :
    RegularAt a u := by
  rw [← RatFunc.num_div_denom u]
  exact ⟨_, RadiusValue.fraction _ _ h⟩

/-- The local parameter r-a, considered as a rational function. -/
def coordinate (a : ℂ) : ℂᵣ := ι (localCoordinate a)

theorem coordinate_ne_zero (a : ℂ) : coordinate a ≠ 0 :=
  RatFunc.algebraMap_ne_zero (localCoordinate_ne_zero a)

theorem coordinate_eq (a : ℂ) : coordinate a = R - Cᵣ a := by
  simp [coordinate, localCoordinate]

@[simp] theorem coordinate_zero : coordinate 0 = R := by simp [coordinate_eq]

theorem coordinate_value (a : ℂ) : RadiusValue a (coordinate a) 0 := by
  simpa [coordinate, localCoordinate] using RadiusValue.polynomial a (localCoordinate a)

@[simp] theorem coordinate_derivative (a : ℂ) : δ (coordinate a) = 1 := by
  simp [coordinate_eq, rationalDerivative_sub]

theorem coordinate_zpow_value (a : ℂ) (m : ℤ) (hm : 0 ≤ m) :
    RadiusValue a ((coordinate a)^m) (if m = 0 then 1 else 0) := by
  lift m to ℕ using hm
  simpa [zero_pow_eq] using (coordinate_value a).pow m

theorem coordinate_zpow_positive (a : ℂ) {m : ℤ} (hm : 0 < m) : RadiusValue a ((coordinate a)^m) 0 := by
  simpa [ne_of_gt hm] using coordinate_zpow_value a m hm.le

theorem regular_of_coordinate_mul_zero {a : ℂ} {u : ℂᵣ}
    (h : RadiusValue a (coordinate a*u) 0) : RegularAt a u := by
  obtain ⟨p,q,hq,he,hv⟩ := h
  have hp := (div_eq_zero_iff.mp hv.symm).resolve_right hq
  obtain ⟨r,hr⟩ := dvd_iff_isRoot.mpr (show IsRoot p a from hp)
  change p = localCoordinate a*r at hr
  rw [hr, map_mul, mul_div_assoc] at he
  have eq := mul_left_cancel₀ (coordinate_ne_zero a) he
  rw [eq]
  exact ⟨_, RadiusValue.fraction _ _ hq⟩

theorem coordinate_zpow_derivative (a : ℂ) (m : ℤ) :
    δ ((coordinate a)^m) = (m:ℂᵣ)*(coordinate a)^(m-1) := by
  let t := coordinate a
  have ht : t ≠ 0 := coordinate_ne_zero a
  have hd : δ t = 1 := coordinate_derivative a
  have pos (n : ℕ) : t * δ (t^n) = (n : ℂᵣ) * t^n := by
    cases n with
    | zero => simp
    | succ n =>
      rw [rationalDerivative_pow, hd, mul_one, Nat.succ_sub_one, pow_succ]
      ring
  have inv {v c : ℂᵣ} (hv : v ≠ 0) (h : t*δ v = c*v) :
      t*δ (v⁻¹) = (-c)*v⁻¹ := by
    rw [rationalDerivative_inv, ← mul_div_assoc, mul_neg, h]
    field_simp
  have he : t * δ (t^m) = (m : ℂᵣ) * t^m := by
    cases m with
    | ofNat n => simpa using pos n
    | negSucc n =>
      have hc : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
      rw [hc, zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast]
      exact inv (pow_ne_zero _ ht) (pos (n+1))
  have hz : t*t^(m-1) = t^m := calc
    _ = t^(1:ℤ)*t^(m-1) := by rw [zpow_one]
    _ = _ := by rw [← zpow_add₀ ht, show 1+(m-1)=m by omega]
  change δ (t^m) = _
  apply mul_left_cancel₀ ht
  rw [he, mul_left_comm t, hz]

theorem derivative_of_leading_power (a : ℂ) (m : ℤ) (v : ℂᵣ) :
    δ ((coordinate a)^m*v) = (coordinate a)^(m-1) * ((m:ℂᵣ)*v+coordinate a*δ v) := by
  have he : (coordinate a)^m = (coordinate a)^(m-1) * coordinate a := by
    simpa only [sub_add_cancel, zpow_one] using (zpow_add₀ (coordinate_ne_zero a) (m-1) 1)
  conv_lhs => rw [rationalDerivative_mul, coordinate_zpow_derivative]
  rw [he]
  ring

def finiteOrder (u : ℂᵣ) (a : ℂ) : ℤ :=
  (rootMultiplicity a u.num : ℤ) - (rootMultiplicity a u.denom : ℤ)

theorem leading_at_finite (u : ℂᵣ) (hu : u ≠ 0) (a : ℂ) :
    ∃ v : ℂᵣ, ∃ c : ℂ, c ≠ 0 ∧ RadiusValue a v c ∧ u = (coordinate a)^(finiteOrder u a)*v := by
  obtain ⟨p, hp, hp'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd u.num (RatFunc.num_ne_zero hu) a
  obtain ⟨q, hq, hq', _⟩ := normalized_denominator u a
  have hp'' : p.eval a ≠ 0 := fun h => hp' (dvd_iff_isRoot.mpr h)
  refine ⟨ι p / ι q, p.eval a / q.eval a, div_ne_zero hp'' hq', RadiusValue.fraction p q hq', ?_⟩
  change u.num = localCoordinate a ^ rootMultiplicity a u.num * p at hp
  rw [finiteOrder, zpow_natCast_sub_natCast₀ (coordinate_ne_zero a)]
  conv_lhs => rw [← RatFunc.num_div_denom u, hp, hq]
  simp only [map_mul, map_pow, coordinate]
  rw [div_mul_div_comm]

theorem nonnegative_power_of_regular {a : ℂ} {u v : ℂᵣ} {m : ℤ} {c : ℂ}
    (hu : RegularAt a u) (hv : RadiusValue a v c) (hc : c ≠ 0)
    (he : u = (coordinate a)^m*v) : 0 ≤ m := by
  by_contra! h
  obtain ⟨d,hd⟩ := hu
  have r := (coordinate_zpow_positive a (show 0 < -m by omega)).mul hd
  have eq : (coordinate a)^(-m)*u = v := by
    rw [he, ← mul_assoc, ← zpow_add₀ (coordinate_ne_zero a), neg_add_cancel, zpow_zero, one_mul]
  rw [eq, zero_mul] at r
  exact hc (hv.unique r)

theorem zero_power_of_nonzero_value {a : ℂ} {u v : ℂᵣ} {m : ℤ} {c d : ℂ}
    (hu : RadiusValue a u d) (hd : d ≠ 0) (hv : RadiusValue a v c) (hc : c ≠ 0)
    (he : u = (coordinate a)^m*v) : m = 0 := by
  have hm := nonnegative_power_of_regular ⟨_, hu⟩ hv hc he
  by_contra hn
  have h := (coordinate_zpow_positive a (show 0 < m by omega)).mul hv
  rw [← he, zero_mul] at h
  exact hd (hu.unique h)

theorem radiusValue_of_reciprocal_polynomial (p : ℂ[X]) (hp : p ≠ 0)
    (hr : RegularAt 0 (reciprocalHom (ι p))) : p.natDegree = 0 := by
  have eq : reciprocalHom (ι p) = R^(-(p.natDegree:ℤ))*ι p.reverse := by
    rw [reciprocalHom_polynomial, Polynomial.aeval_def, polynomial_reciprocal, zpow_neg, zpow_natCast]
    simp [div_eq_mul_inv, mul_comm]
  have leading : p.reverse.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hp
  rw [← coordinate_zero] at eq
  have hg := nonnegative_power_of_regular hr (RadiusValue.polynomial 0 p.reverse) leading eq
  omega

#print axioms RadiusValue.denom_ne_zero
#print axioms leading_at_finite
#print axioms zero_power_of_nonzero_value
#print axioms radiusValue_of_reciprocal_polynomial

end

end SchwarzschildLaurent
