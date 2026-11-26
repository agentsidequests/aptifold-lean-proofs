import FixedParentIndependence
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Meromorphic germs realize the differential field used for the fixed parent. -/
namespace SchwarzschildLaurent
namespace MeromorphicRadial

open Filter Polynomial
open scoped Topology

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "δ" => rationalDerivative

abbrev GermAt (r : ℂ) := Filter.Germ (𝓝[≠] r) ℂ

def meromorphicSubring (r : ℂ) : Subring (GermAt r) where
  carrier := {g | ∃ f : ℂ → ℂ, MeromorphicAt f r ∧ (f : GermAt r) = g}
  zero_mem' := ⟨fun _ => 0, MeromorphicAt.const 0 r, rfl⟩
  one_mem' := ⟨fun _ => 1, MeromorphicAt.const 1 r, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g,hf.add hg,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩
  neg_mem' := by
    rintro _ ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩

abbrev At (r : ℂ) := ↥(meromorphicSubring r)

def ofFunction {r : ℂ} (f : ℂ→ℂ) (hf : MeromorphicAt f r) : At r :=
  ⟨(f : GermAt r),⟨f,hf,rfl⟩⟩

theorem ofFunction_eq {r : ℂ} {f g : ℂ→ℂ} (hf : MeromorphicAt f r) (hg : MeromorphicAt g r) :
    ofFunction f hf = ofFunction g hg ↔ f =ᶠ[𝓝[≠] r] g :=
  ⟨fun h => Filter.Germ.coe_eq.mp (congrArg Subtype.val h),
    fun h => Subtype.ext (Filter.Germ.coe_eq.mpr h)⟩

private theorem represented {r : ℂ} (u : At r) :
    ∃ f : ℂ→ℂ, ∃ hf : MeromorphicAt f r, u = ofFunction f hf := by
  obtain ⟨f,hf,h⟩ := u.property
  exact ⟨f,hf,Subtype.ext h.symm⟩

private theorem meromorphic_isField (r : ℂ) : IsField (At r) where
  exists_pair_ne := ⟨0,1,fun e => (zero_ne_one : (0:GermAt r)≠1) (congrArg Subtype.val e)⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro u hu
    obtain ⟨f,hf,rfl⟩ := represented u
    have hn : ∀ᶠ z in 𝓝[≠] r, f z≠0 := hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left (by
      intro hz
      apply hu
      exact (ofFunction_eq hf (MeromorphicAt.const 0 r)).2 hz)
    refine ⟨ofFunction f⁻¹ hf.inv,Subtype.ext ?_⟩
    change ((fun z => f z*(f z)⁻¹) : GermAt r) = ((fun _ : ℂ => (1:ℂ)) : GermAt r)
    exact Filter.Germ.coe_eq.mpr (hn.mono fun _ hz => mul_inv_cancel₀ hz)

instance (r : ℂ) : Field (At r) := (meromorphic_isField r).toField

private def germDerivative (r : ℂ) : GermAt r → GermAt r :=
  Filter.Germ.map' _root_.deriv (fun _ _ h => h.nhdsNE_deriv)

def pointDerivative (r : ℂ) : At r →+ At r where
  toFun u := ⟨germDerivative r u.val, by
    obtain ⟨f,hf,rfl⟩ := represented u
    exact ⟨_root_.deriv f,hf.deriv,rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    change ((_root_.deriv (fun _ : ℂ => (0:ℂ))) : GermAt r) = ((fun _ : ℂ => (0:ℂ)) : GermAt r)
    rw [deriv_const']
  map_add' u v := by
    obtain ⟨f,hf,rfl⟩ := represented u
    obtain ⟨g,hg,rfl⟩ := represented v
    apply Subtype.ext
    change ((_root_.deriv (f+g)) : GermAt r) = (fun z => _root_.deriv f z+_root_.deriv g z)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hfz hgz
    exact deriv_fun_add hfz.differentiableAt hgz.differentiableAt

@[simp] theorem pointDerivative_ofFunction {r : ℂ} (f : ℂ→ℂ) (hf : MeromorphicAt f r) :
    pointDerivative r (ofFunction f hf) = ofFunction (_root_.deriv f) hf.deriv := rfl

theorem pointDerivative_mul (r : ℂ) (u v : At r) :
    pointDerivative r (u*v) = pointDerivative r u*v+u*pointDerivative r v := by
  obtain ⟨f,hf,rfl⟩ := represented u
  obtain ⟨g,hg,rfl⟩ := represented v
  apply Subtype.ext
  change ((_root_.deriv (f*g)) : GermAt r) = (fun z => _root_.deriv f z*g z+f z*_root_.deriv g z)
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hfz hgz
  exact deriv_fun_mul hfz.differentiableAt hgz.differentiableAt

private theorem pointDerivative_div (r : ℂ) (u v : At r) (hv : v≠0) :
    pointDerivative r (u/v) = (pointDerivative r u*v-u*pointDerivative r v)/v^2 := by
  have h := pointDerivative_mul r (u/v) v
  rw [div_mul_cancel₀ _ hv] at h
  apply (eq_div_iff (pow_ne_zero 2 hv)).mpr
  have h' := div_mul_cancel₀ u hv
  linear_combination -v*h-pointDerivative r v*h'

private theorem polynomial_meromorphic (r : ℂ) (p : ℂ[X]) : MeromorphicAt p.eval r := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add] using hp.fun_add hq
  | monomial n c =>
    simpa only [eval_monomial,id_eq] using (MeromorphicAt.const c r).fun_mul ((MeromorphicAt.id r).fun_pow n)

def polynomialGerm (r : ℂ) : ℂ[X] →+* At r where
  toFun p := ofFunction p.eval (polynomial_meromorphic r p)
  map_zero' := Subtype.ext (Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => eval_zero (x := z)))
  map_one' := Subtype.ext (Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => eval_one (x := z)))
  map_add' p q := Subtype.ext (Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => eval_add))
  map_mul' p q := Subtype.ext (Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => eval_mul))

theorem polynomialGerm_injective (r : ℂ) : Function.Injective (polynomialGerm r) := by
  intro p q eq
  apply sub_eq_zero.mp
  have hz : polynomialGerm r (p-q)=0 := by rw [map_sub,eq,sub_self]
  by_contra nonzero
  obtain ⟨s,hs,hs'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p-q) nonzero r
  have sn : s.eval r ≠ 0 := fun e => hs' (dvd_iff_isRoot.mpr e)
  have cont : ContinuousAt s.eval r := (s.hasDerivAt r).continuousAt
  have ev : ∀ᶠ z in 𝓝[≠] r, s.eval z≠0 := by
    exact nhdsWithin_le_nhds (cont.eventually (eventually_ne_nhds sn))
  have zero := congrArg Subtype.val hz
  change ((p-q).eval : GermAt r) = ((fun _ : ℂ => (0:ℂ)) : GermAt r) at zero
  have bad := Filter.Germ.coe_eq.mp zero
  have impossible : ∀ᶠ z in 𝓝[≠] r, False := by
    filter_upwards [ev,bad,self_mem_nhdsWithin] with z zval zzero zne
    have hr : z-r≠0 := sub_ne_zero.mpr (by simpa using zne)
    rw [hs,eval_mul,eval_pow,eval_sub,eval_X,eval_C] at zzero
    exact (mul_ne_zero (pow_ne_zero _ hr) zval) zzero
  exact impossible.exists.choose_spec

def rationalGerm (r : ℂ) : ℂᵣ →+* At r :=
  IsFractionRing.lift (polynomialGerm_injective r)

theorem rationalGerm_polynomial (r : ℂ) (p : ℂ[X]) :
    rationalGerm r (ι p) = polynomialGerm r p :=
  IsFractionRing.lift_algebraMap (polynomialGerm_injective r) p

theorem pointDerivative_rationalGerm (r : ℂ) (u : ℂᵣ) :
    pointDerivative r (rationalGerm r u) = rationalGerm r (δ u) := by
  have pder (p : ℂ[X]) : pointDerivative r (polynomialGerm r p) = polynomialGerm r p.derivative := by
    apply Subtype.ext
    change ((_root_.deriv p.eval) : GermAt r) = p.derivative.eval
    exact Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => (p.hasDerivAt z).deriv)
  let e := rationalGerm r
  refine RatFunc.induction_on
    (P := fun y => pointDerivative r (rationalGerm r y) = rationalGerm r (δ y)) u ?_
  intro p q hq
  have qne : polynomialGerm r q ≠ 0 := fun eq =>
    hq (polynomialGerm_injective r (eq.trans (map_zero (polynomialGerm r)).symm))
  rw [rationalDerivative_fraction p q hq,map_div₀,rationalGerm_polynomial,rationalGerm_polynomial,
    pointDerivative_div _ _ _ qne]
  simp only [pder,map_div₀,map_pow,rationalGerm_polynomial,map_sub,map_mul]

def differentialField (r : ℂ) : RadialDifferentialField (At r) where
  embed := rationalGerm r
  deriv :=
    { toFun := fun u => rationalGerm r radialFactor*pointDerivative r u
      map_zero' := by rw [map_zero,mul_zero]
      map_add' := by intro u v; rw [map_add,mul_add] }
  product := by
    intro u v
    simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk,pointDerivative_mul]
    ring
  compatible := by
    intro u
    simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk,pointDerivative_rationalGerm,tortoiseDerivative,map_mul]

theorem tortoise_ofFunction {r : ℂ} (f : ℂ→ℂ) (hf : MeromorphicAt f r) :
    (differentialField r).deriv (ofFunction f hf) =
      rationalGerm r radialFactor*ofFunction (_root_.deriv f) hf.deriv := rfl

#print axioms polynomialGerm_injective
#print axioms pointDerivative_rationalGerm
#print axioms differentialField

end

end MeromorphicRadial
end SchwarzschildLaurent
