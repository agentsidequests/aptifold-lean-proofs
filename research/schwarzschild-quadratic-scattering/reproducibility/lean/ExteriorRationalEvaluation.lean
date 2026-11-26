import RationalLocalValues
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv

/-! Evaluation on the real exterior, with a nonvanishing denominator
as the premise for the algebra and the ordinary radial derivative. -/
namespace SchwarzschildLaurent.Exterior

open Polynomial

noncomputable section

local notation "ℂᵣ" => RatFunc ℂ
local notation "ι" => (algebraMap ℂ[X] ℂᵣ)
local notation "δ" => rationalDerivative

def radialEval (u : ℂᵣ) (r : ℝ) : ℂ := RatFunc.eval (RingHom.id ℂ) (r : ℂ) u

theorem radius_value_eval {z c : ℂ} {u : ℂᵣ} (h : RadiusValue z u c) :
    RatFunc.eval (RingHom.id ℂ) z u = c := by
  have q := RadiusValue.fraction u.num u.denom h.denom_ne_zero
  rw [RatFunc.num_div_denom] at q
  simpa only [RatFunc.eval,Polynomial.eval₂_id] using q.unique h

theorem radial_eval_derivative {r : ℝ} {u : ℂᵣ} {c : ℂ} (h : RadiusValue (r : ℂ) u c) :
    HasDerivAt (radialEval u) (radialEval (δ u) r) r := by
  let z : ℂ := r
  let p := u.num
  let q := u.denom
  have hq : q.eval z ≠ 0 := h.denom_ne_zero
  let numerator := p.derivative*q-p*q.derivative
  have form : δ u = ι numerator / ι (q^2) := by
    simp only [rationalDerivative,numerator,p,q,map_pow]
  have dh := RadiusValue.fraction (a := z) numerator (q^2) (by simp [hq] : (q^2).eval z ≠ 0)
  rw [← form] at dh
  have value : radialEval (δ u) r =
      (p.derivative.eval z*q.eval z-p.eval z*q.derivative.eval z)/(q.eval z)^2 := by
    simpa only [radialEval,numerator,eval_sub,eval_mul,eval_pow] using radius_value_eval dh
  rw [value]
  change HasDerivAt (fun t : ℝ => p.eval (t : ℂ)/q.eval (t : ℂ)) _ r
  exact ((p.hasDerivAt z).div (q.hasDerivAt z) hq).comp_ofReal

def readRow (p : Row ℂᵣ) (r : ℝ) : Row ℂ := mapRow (fun u => radialEval u r) p

def RowValues (r : ℝ) (p : Row ℂᵣ) (v : Row ℂ) : Prop :=
  RadiusValue (r : ℂ) p.1 v.1 ∧ RadiusValue (r : ℂ) p.2.1 v.2.1 ∧ RadiusValue (r : ℂ) p.2.2 v.2.2

abbrev RegularRow (r : ℝ) (p : Row ℂᵣ) : Prop := RowValues r p (readRow p r)

namespace RowValues

variable {r : ℝ} {p q : Row ℂᵣ} {a b : Row ℂ}

theorem read_eq (h : RowValues r p a) : readRow p r = a :=
  Prod.ext (radius_value_eval h.1) (Prod.ext (radius_value_eval h.2.1) (radius_value_eval h.2.2))

theorem regular (h : RowValues r p a) : RegularRow r p := by
  show RowValues r p (readRow p r)
  rw [h.read_eq]
  exact h

theorem fraction (p : Row ℂ[X]) (q : ℂ[X]) (r : ℝ) (hq : q.eval (r : ℂ) ≠ 0) :
    RegularRow r (fractionRow p q) :=
  (show RowValues r (fractionRow p q) (mapRow (fun v : ℂ[X] => v.eval (r : ℂ)/q.eval (r : ℂ)) p) from
    ⟨RadiusValue.fraction _ _ hq,RadiusValue.fraction _ _ hq,RadiusValue.fraction _ _ hq⟩).regular

theorem plus (h : RowValues r p a) (g : RowValues r q b) :
    RowValues r (SchwarzschildLaurent.plus p q) (SchwarzschildLaurent.plus a b) :=
  ⟨h.1.add g.1,h.2.1.add g.2.1,h.2.2.add g.2.2⟩

theorem minus (h : RowValues r p a) (g : RowValues r q b) :
    RowValues r (SchwarzschildLaurent.minus p q) (SchwarzschildLaurent.minus a b) :=
  ⟨h.1.sub g.1,h.2.1.sub g.2.1,h.2.2.sub g.2.2⟩

theorem scale {u : ℂᵣ} {c : ℂ} (h : RadiusValue (r : ℂ) u c) (g : RowValues r p a) :
    RowValues r (SchwarzschildLaurent.scale u p) (SchwarzschildLaurent.scale c a) :=
  ⟨h.mul g.1,h.mul g.2.1,h.mul g.2.2⟩

theorem jet {u v w : ℂᵣ} {U V W : ℂ}
    (hu : RadiusValue (r : ℂ) u U) (hv : RadiusValue (r : ℂ) v V)
    (hw : RadiusValue (r : ℂ) w W) (h : RowValues r p a) :
    RowValues r (SchwarzschildLaurent.jet u v w p) (SchwarzschildLaurent.jet U V W a) := by
  have two : RadiusValue (r : ℂ) (2:ℂᵣ) 2 := by
    simpa only [map_ofNat] using RadiusValue.const (r : ℂ) 2
  exact ⟨hu.mul h.2.1,
    (((two.mul hw).mul h.1).add (hv.mul h.2.1)).add ((two.mul hu).mul h.2.2),
    (hw.mul h.2.1).add ((two.mul hv).mul h.2.2)⟩

theorem derivative (h : RowValues r p a) : RegularRow r (rationalRowDerivative p) := by
  obtain ⟨A,hA⟩ := h.1.derivative
  obtain ⟨B,hB⟩ := h.2.1.derivative
  obtain ⟨C,hC⟩ := h.2.2.derivative
  exact (show RowValues r (rationalRowDerivative p) (A,B,C) from ⟨hA,hB,hC⟩).regular

theorem unscaled (h : RowValues r p a) :
    RowValues r (unscaledRow p) (a.1,a.2.1*(r : ℂ)^2,a.2.2*(r : ℂ)^4) :=
  ⟨h.1,h.2.1.mul ((RadiusValue.radius (r : ℂ)).pow 2),h.2.2.mul ((RadiusValue.radius (r : ℂ)).pow 4)⟩

end RowValues

#print axioms radius_value_eval
#print axioms radial_eval_derivative

end
end SchwarzschildLaurent.Exterior
