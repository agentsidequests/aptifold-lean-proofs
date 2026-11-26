import VacuumRadialData
import MixedFormulaEvaluation
import PureOddPhysicalDomain

namespace SchwarzschildEinstein.PureOdd.Vacuum

open SchwarzschildLaurent SchwarzschildMixtures.ExactRational SchwarzschildMixtures.PureOddProgram
open SchwarzschildMixtures (Expr)

noncomputable section

theorem map_jet_entry {A B : Type} (g : A → B) (z : A) (T P : RadialJet A)
    (E : Mixed.PolarParentJets A) (i : Nat) :
    g (jetEntry z T P E i) = jetEntry (g z) (mapJet g T) (mapJet g P) (Mixed.mapPolarJets g E) i := by
  unfold jetEntry
  split <;> rfl

variable {K : Type} [Field K] (d : K → K) (r k ell : K)

local notation "F" => Formula.interpret d r k ell
local notation "L" => mapLinear F

private theorem interpreted_entry (i : Nat) :
    L (reconstructedEntry Formula.dr .radius .frequency .angular i) =
      reconstructedEntry d r k ell i := by
  have hr : F .radius = r := rfl
  have hk : F .frequency = k := rfl
  have he : F .angular = ell := rfl
  have hz : L (Nat.cast 0, Nat.cast 0) = ((0 : K), (0 : K)) := by
    simp [mapLinear, Nat.cast, Formula.interpret]
  unfold reconstructedEntry
  rw [map_jet_entry L _ _ _ _ i]
  simp only [eval_parent_jet, eval_time_amplitude,
    eval_radius_amplitude, Mixed.eval_polar, hr, hk, he, hz, Nat.cast_zero]

theorem interpreted_coefficient (terms : List RadialMonomial) :
    L (coefficientProgram terms) =
      radialCoefficient (fun q => (q : K)) r k ell (reconstructedEntry d r k ell) terms := by
  induction terms with
  | nil => simp [coefficientProgram, radialCoefficient, mapLinear, Nat.cast, Formula.interpret]
  | cons t ts ih =>
    have hadd (a b : Linear Formula) :
        L (Mixed.linearAdd a b) = Mixed.linearAdd (L a) (L b) := rfl
    have hscale (a : Formula) (b : Linear Formula) :
        L (Mixed.linearScale a b) = Mixed.linearScale (F a) (L b) := rfl
    have weight : F (radialWeight Mixed.rationalConstant .radius .frequency .angular t) =
        radialWeight (fun q => (q : K)) r k ell t := by
      simp only [radialWeight, Formula.interpret_mul, Formula.interpret_pow, Mixed.eval_rat,
        Formula.interpret]
    change L (Mixed.linearAdd
      (Mixed.linearScale (radialWeight Mixed.rationalConstant .radius .frequency .angular t)
        (reconstructedEntry Formula.dr .radius .frequency .angular t.jet))
      (coefficientProgram ts)) = _
    rw [hadd, hscale, weight, interpreted_entry, ih]
    rfl

local notation "ℂᵣ" => RatFunc ℂ
local notation "R" => (RatFunc.X : ℂᵣ)
local notation "Cᵣ" => (RatFunc.C : ℂ →+* ℂᵣ)

theorem interpreted_extension (embed : ℂᵣ →+* K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u)) (w e : ℂ) (f : Formula) :
    Formula.interpret d (embed R) (embed (Cᵣ w)) (embed (Cᵣ e)) f = embed (f.value w e) := by
  induction f <;> simp only [Formula.interpret, Formula.value, map_intCast, map_add, map_mul,
    map_div₀, map_neg, *]

theorem formula_zero (f : Formula) (proof : zeroCertificate f)
    (n : ℕ) (hn : 2 ≤ n) (w : ℂ) (wi : w.re = 0) : f.value w n = 0 := by
  obtain ⟨p, h, h0⟩ := proof
  rw [(h.sound w n (physical_divisors_nonzero n hn w wi)).1]
  simp [Fraction.value, Expr.value_eq_of_check _ _ h0, Expr.value_constant]

theorem radial_coefficient_zero (embed : ℂᵣ →+* K)
    (compatible : ∀ u, d (embed u) = embed (rationalDerivative u))
    (n : ℕ) (hn : 2 ≤ n) (w : ℂ) (wi : w.re = 0)
    (ts : List RadialMonomial) (checked : vanishingCertificate ts) :
    let r := embed R
    let k := embed (Cᵣ w)
    let ell := embed (Cᵣ (n:ℂ))
    radialCoefficient (fun q => (q : K)) r k ell (reconstructedEntry d r k ell) ts = (0,0) := by
  dsimp only
  rw [← interpreted_coefficient d (embed R) (embed (Cᵣ w)) (embed (Cᵣ (n:ℂ))) ts]
  exact Prod.ext
    (by simp only [mapLinear, interpreted_extension d embed compatible,
      formula_zero _ checked.1 n hn w wi, map_zero])
    (by simp only [mapLinear, interpreted_extension d embed compatible,
      formula_zero _ checked.2 n hn w wi, map_zero])

#print axioms interpreted_coefficient
#print axioms radial_coefficient_zero

end
end SchwarzschildEinstein.PureOdd.Vacuum
