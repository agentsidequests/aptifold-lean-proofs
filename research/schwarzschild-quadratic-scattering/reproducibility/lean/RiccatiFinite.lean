import RationalLocalValues
import RiccatiAlgebra

/-! Finite pole orders and residues for the parent's log derivative. -/
namespace SchwarzschildLaurent

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)
local notation "δ" => rationalDerivative

def radiusProduct : ℂᵣ := R*(R-2)

def LogDerivativeEquation (h k : ℂ) (z : ℂᵣ) : Prop :=
  radiusProduct^2*(δ z+z^2) + 2*radiusProduct*z = ι (jetA h k)

theorem shifted_radius_ne_zero (a : ℂ) : R-Cᵣ a ≠ 0 := by
  simpa only [coordinate_eq] using coordinate_ne_zero a

theorem radius_minus_two_ne_zero : R-2 ≠ 0 := by
  simpa only [map_ofNat] using shifted_radius_ne_zero 2

theorem radialFactor_ne_zero : radialFactor ≠ 0 :=
  div_ne_zero radius_minus_two_ne_zero RatFunc.X_ne_zero

private theorem radialFactor_deriv : δ radialFactor = 2/R^2 := by
  have htwo : δ (2:ℂᵣ) = 0 := by simpa only [map_ofNat] using rationalDerivative_constant 2
  simp only [radialFactor, rationalDerivative_div, rationalDerivative_sub, rationalDerivative_radius,
    htwo, sub_zero, one_mul, mul_one]
  ring

theorem logDerivativeEquation_of_riccati {h k : ℂ} {u : ℂᵣ} (hu : RationalRiccati h k u) :
    LogDerivativeEquation h k (u/radialFactor) := by
  let z := u/radialFactor
  have hz : radialFactor*z = u := by dsimp [z]; exact mul_div_cancel₀ _ radialFactor_ne_zero
  have expr : R^4*(tortoiseDerivative (radialFactor*z)+(radialFactor*z)^2) =
      radiusProduct^2*(δ z+z^2)+2*radiusProduct*z := by
    simp only [tortoiseDerivative, rationalDerivative_mul, radialFactor_deriv]
    simp only [radialFactor, radiusProduct]
    field_simp [RatFunc.X_ne_zero]
    ring
  have term : R^4*parentTerm h k = ι (jetA h k) := by
    simp only [parentTerm, jetA, oddPotential, radialFactor, map_add, map_sub, map_mul, map_pow,
      RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_ofNat]
    field_simp [RatFunc.X_ne_zero]
    ring
  unfold RationalRiccati at hu
  unfold LogDerivativeEquation
  rw [← expr, hz, hu, term]

private theorem int_value (a : ℂ) (m : ℤ) : RadiusValue a (m:ℂᵣ) (m:ℂ) := by
  simpa only [map_intCast] using RadiusValue.const a (m:ℂ)

private theorem two_value (a : ℂ) : RadiusValue a (2:ℂᵣ) 2 := by
  simpa only [map_ofNat] using RadiusValue.const a 2

private theorem radius_sub_two_value (a : ℂ) : RadiusValue a (R-2) (a-2) :=
  (RadiusValue.radius a).sub (two_value a)

private theorem radiusProduct_value (a : ℂ) : RadiusValue a radiusProduct (a*(a-2)) :=
  (RadiusValue.radius a).mul (radius_sub_two_value a)

/-- Balance after factoring the leading powers of r-a out of the log derivative
and the coefficient that vanishes at the origin and horizon. -/
private theorem rescaled_log_eq {h k a : ℂ} {z v g : ℂᵣ} {m p : ℤ}
    (eq : LogDerivativeEquation h k z) (hz : z = (coordinate a)^m*v)
    (hg : radiusProduct = (coordinate a)^p*g) :
    let t := coordinate a
    g^2*(t^(-m-1)*((m:ℂᵣ)*v+t*δ v)+v^2) + 2*g*t^(-m-p)*v =
      t^(-2*m-2*p)*ι (jetA h k) := by
  let t := coordinate a
  let n := -2*m-2*p
  let v' := (m:ℂᵣ)*v+t*δ v
  have ht : t ≠ 0 := coordinate_ne_zero a
  unfold LogDerivativeEquation at eq
  rw [hz, hg, derivative_of_leading_power] at eq
  change (t^p*g)^2*(t^(m-1)*v'+(t^m*v)^2)+2*(t^p*g)*(t^m*v) = _ at eq
  change g^2*(t^(-m-1)*v'+v^2)+2*g*t^(-m-p)*v = t^n*_
  calc
    _ = t^n*((t^p*g)^2*(t^(m-1)*v'+(t^m*v)^2)+2*(t^p*g)*(t^m*v)) := by
      symm
      calc
        _ = (t^n*t^p*t^p*t^(m-1))*g^2*v' +
          (t^n*t^p*t^p*t^m*t^m)*g^2*v^2 + 2*g*(t^n*t^p*t^m)*v := by ring
        _ = _ := by
          simp only [← zpow_add₀ ht]
          rw [show n+p+p+(m-1) = -m-1 by dsimp [n]; omega,
            show n+p+p+m+m = 0 by dsimp [n]; omega,
            show n+p+m = -m-p by dsimp [n]; omega, zpow_zero]
          ring
    _ = _ := congrArg (fun x => t^n*x) eq

private theorem log_eq_simple_pole {h k a : ℂ} {z g : ℂᵣ} {p : ℤ} {cg : ℂ}
    (eq : LogDerivativeEquation h k z) (hg : radiusProduct = (coordinate a)^p*g)
    (gp : RadiusValue a g cg) (hg0 : cg ≠ 0) (hp : p = 0 ∨ p = 1) :
    RegularAt a (coordinate a*z) := by
  let t := coordinate a
  by_cases hz : z = 0
  · exact ⟨0, by simpa [hz] using RadiusValue.zero a⟩
  obtain ⟨v,c,hc,hv,hev⟩ := leading_at_finite z hz a
  let m := finiteOrder z a
  change z = t^m*v at hev
  have hm : -1 ≤ m := by
    by_contra! bad
    have res := rescaled_log_eq eq hev hg
    obtain ⟨d,hd⟩ := hv.derivative
    have first := (coordinate_zpow_positive a (show 0 < -m-1 by omega)).mul
      (((int_value a m).mul hv).add ((coordinate_value a).mul hd))
    have second := (((two_value a).mul gp).mul
      (coordinate_zpow_positive a (show 0 < -m-p by omega))).mul hv
    have rhs := (coordinate_zpow_positive a (show 0 < -2*m-2*p by omega)).mul
      (RadiusValue.polynomial a (jetA h k))
    have lhs := ((gp.pow 2).mul (first.add (hv.pow 2))).add second
    dsimp only at res
    rw [res] at lhs
    have contradiction := lhs.unique rhs
    simp only [zero_mul, zero_add, mul_zero, add_zero] at contradiction
    exact (mul_ne_zero (pow_ne_zero 2 hg0) (pow_ne_zero 2 hc)) contradiction
  have newOrder : t*z = t^(m+1)*v := by
    rw [hev, zpow_add₀ (coordinate_ne_zero a), zpow_one]
    ring
  rw [newOrder]
  exact ⟨_, (coordinate_zpow_value a _ (by omega)).mul hv⟩

private theorem rescaled_residue {h k a : ℂ} {z g : ℂᵣ} {p : ℤ} {cg : ℂ}
    (eq : LogDerivativeEquation h k z) (hg : radiusProduct = (coordinate a)^p*g)
    (gp : RadiusValue a g cg) (hg0 : cg ≠ 0) (hp : p = 0 ∨ p = 1) :
    ∃ c, RadiusValue a (coordinate a*z) c ∧
      cg^2*(c^2-c) + (if p = 1 then 2*cg*c else 0) =
        (if p = 1 then (jetA h k).eval a else 0) := by
  obtain ⟨c,hc⟩ := log_eq_simple_pole eq hg gp hg0 hp
  let t := coordinate a
  let v := t*z
  have hv : z = t^(-1:ℤ)*v := by
    rw [zpow_neg_one, ← mul_assoc, inv_mul_cancel₀ (coordinate_ne_zero a), one_mul]
  have res := rescaled_log_eq eq hv hg
  obtain ⟨d,hd⟩ := hc.derivative
  have first := (coordinate_zpow_value a (-(-1)-1) (by omega)).mul
    (((int_value a (-1)).mul hc).add ((coordinate_value a).mul hd))
  have second := (((two_value a).mul gp).mul
    (coordinate_zpow_value a (-(-1)-p) (by omega))).mul hc
  have rhs := (coordinate_zpow_value a (-2*(-1)-2*p) (by omega)).mul
    (RadiusValue.polynomial a (jetA h k))
  have lhs := ((gp.pow 2).mul (first.add (hc.pow 2))).add second
  change RadiusValue a _ _ at lhs
  dsimp only at res
  rw [res] at lhs
  have value := lhs.unique rhs
  refine ⟨c,hc,?_⟩
  rcases hp with rfl | rfl <;> norm_num [-mul_eq_zero, -pow_eq_zero_iff] at value ⊢ <;>
    linear_combination value

theorem ordinary_log_residue {h k a : ℂ} {z : ℂᵣ} (h0 : a ≠ 0) (h2 : a ≠ 2)
    (eq : LogDerivativeEquation h k z) :
    ∃ c, RadiusValue a (coordinate a*z) c ∧ (c = 0 ∨ c = 1) := by
  have hprod : radiusProduct = (coordinate a)^(0:ℤ)*radiusProduct := by simp
  obtain ⟨c,hc,he⟩ := rescaled_residue eq hprod (radiusProduct_value a)
    (mul_ne_zero h0 (sub_ne_zero.mpr h2)) (Or.inl rfl)
  refine ⟨c,hc,?_⟩
  simp only [show (0:ℤ) ≠ 1 by decide, if_false, add_zero] at he
  have e := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 (mul_ne_zero h0 (sub_ne_zero.mpr h2)))
  have fac : c*(c-1) = 0 := by linear_combination e
  simpa only [sub_eq_zero] using mul_eq_zero.mp fac

theorem origin_log_residue {h k : ℂ} {z : ℂᵣ} (eq : LogDerivativeEquation h k z) :
    ∃ c, RadiusValue 0 (coordinate 0*z) c ∧ (c = -1 ∨ c = 3) := by
  have hprod : radiusProduct = (coordinate 0)^(1:ℤ)*(R-2) := by simp [radiusProduct]
  obtain ⟨c,hc,he⟩ := rescaled_residue eq hprod (radius_sub_two_value 0)
    (by norm_num) (Or.inr rfl)
  refine ⟨c,hc,?_⟩
  norm_num [jetA] at he
  have fac : (c+1)*(c-3) = 0 := by linear_combination he/4
  rcases mul_eq_zero.mp fac with h0 | h3
  · exact Or.inl (by linear_combination h0)
  · exact Or.inr (sub_eq_zero.mp h3)

theorem horizon_log_residue {h k : ℂ} {z : ℂᵣ} (eq : LogDerivativeEquation h k z) :
    ∃ c, RadiusValue 2 (coordinate 2*z) c ∧ (c = 2*k ∨ c = -(2*k)) := by
  have hprod : radiusProduct = (coordinate 2)^(1:ℤ)*R := by
    simp only [radiusProduct, coordinate_eq, zpow_one, map_ofNat]
    ring
  obtain ⟨c,hc,he⟩ := rescaled_residue eq hprod (RadiusValue.radius 2)
    (by norm_num) (Or.inr rfl)
  refine ⟨c,hc,?_⟩
  norm_num [jetA] at he
  have fac : (c-2*k)*(c+2*k) = 0 := by linear_combination he/4
  rcases mul_eq_zero.mp fac with hpos | hneg
  · exact Or.inl (sub_eq_zero.mp hpos)
  · exact Or.inr (by linear_combination hneg)

#print axioms logDerivativeEquation_of_riccati
#print axioms ordinary_log_residue
#print axioms origin_log_residue
#print axioms horizon_log_residue

end

end SchwarzschildLaurent
