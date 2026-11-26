import EvenProgram
import MixedFormulaEvaluation

/-! The exported polar expression interprets to the same row obtained
from the curvature table and the metric-source readout. -/
namespace SchwarzschildEinstein.PureOdd.Polar

open Mixed SchwarzschildMixtures.ExactRational SchwarzschildMixtures.PureOddProgram

noncomputable section

variable {K : Type} [DivisionRing K]
variable (d : K → K) (radius frequency angular : K)

local notation "F" => Formula.interpret d radius frequency angular
local notation "L" => mapLinear F
local notation "Q" => mapRow F
local notation "C" => (fun q : Rat => (q : K))

private theorem eval_power (a : Formula) (n : ℕ) :
    F (power (rationalConstant 1) a n) = power (C 1) (F a) n := by
  induction n with
  | zero => exact eval_rat d radius frequency angular 1
  | succ n ih => simp only [power, Formula.interpret_mul, ih]

theorem eval_weight (r invR invH k ell : Formula) (t : JetProduct) :
    F (weight rationalConstant r invR invH k ell t) =
      weight C (F r) (F invR) (F invH) (F k) (F ell) t := by
  have sum (ms : List RadialMonomial) :
      F (ms.foldr (fun m u =>
          rationalConstant m.coefficient * power (rationalConstant 1) r m.radius *
          power (rationalConstant 1) k m.frequency * power (rationalConstant 1) ell m.angular + u)
          (rationalConstant 0)) =
        ms.foldr (fun m u => C m.coefficient * power (C 1) (F r) m.radius *
          power (C 1) (F k) m.frequency * power (C 1) (F ell) m.angular + u) (C 0) := by
    induction ms with
    | nil => exact eval_rat d radius frequency angular 0
    | cons m tail ih =>
      simp only [List.foldr_cons, Formula.interpret_mul, Formula.interpret_add, eval_rat, eval_power, ih]
  simp only [weight, Formula.interpret_mul, eval_power, sum]

theorem eval_jet (E : PolarParentJets (Linear Formula)) (i : Fin 12) :
    L (jetValue E i) = jetValue (mapPolarJets L E) i := by
  have map_if (condition : Prop) [Decidable condition] (a b : Linear Formula) :
      L (if condition then a else b) = if condition then L a else L b := by
    split <;> rfl
  simp only [jetValue, mapPolarJets, mapJet, map_if]

theorem eval_product (u v : Linear Formula) :
    Q (productRow u v) = productRow (L u) (L v) := rfl

private theorem eval_curve (w : JetProduct → Formula) (E : PolarParentJets (Linear Formula)) :
    let a := curveRows rationalConstant w E
    let b := curveRows C (fun t => F (w t)) (mapPolarJets L E)
    (⟨Q a.tt, Q a.rr, Q a.rq, Q a.vv, Q a.qq⟩ : Curvature (Quadratic K)) = b := by
  have entry (ts : List JetProduct) :
      Q (evaluateWith (rationalConstant 0, rationalConstant 0, rationalConstant 0) plus scale
        (fun i j => productRow (jetValue E i) (jetValue E j)) w ts) =
      evaluateWith (C 0, C 0, C 0) plus scale
        (fun i j => productRow (jetValue (mapPolarJets L E) i) (jetValue (mapPolarJets L E) j))
        (fun t => F (w t)) ts := by
    induction ts with
    | nil => simp only [evaluateWith, List.foldr_nil, mapRow, eval_rat]
    | cons t ts ih =>
      simp only [evaluateWith, List.foldr_cons, eval_plus, eval_scale, eval_product, eval_jet] at ih ⊢
      rw [ih]
  simp only [curveRows, tableCurvature, entry]

private theorem eval_readout (r e : Formula) (s : Curvature (Quadratic Formula)) :
    mapSource Q (sourceFromCurvature rationalConstant plus scale r e s) =
      sourceFromCurvature C plus scale (F r) (F e)
        ⟨Q s.tt, Q s.rr, Q s.rq, Q s.vv, Q s.qq⟩ := by
  simp only [sourceFromCurvature, mapSource, eval_plus, eval_scale, eval_rat,
    Formula.interpret_add, Formula.interpret_neg, Formula.interpret_mul, Formula.interpret_div]

theorem eval_source (r k e : Formula) :
    mapSource Q (evenSourceRows rationalConstant Formula.dr r k e) =
      evenSourceRows C d (F r) (F k) (F e) := by
  let w := weight rationalConstant r (rationalConstant 1/r)
    (rationalConstant 1/(r-rationalConstant 2)) k e
  have curve := eval_curve d radius frequency angular w (polarReconstruction Formula.dr r k e)
  simp only [evenSourceRows, eval_readout]
  rw [curve]
  simp only [w, eval_weight, eval_rat, Formula.interpret_div, Formula.interpret_sub, eval_polar]

theorem even_program_value :
    Q Polar.coefficients = bareEvenRows C d radius frequency angular := by
  simp only [Polar.coefficients, bareEvenRows, eval_projected_master, eval_source, Formula.interpret]

#print axioms even_program_value

end
end SchwarzschildEinstein.PureOdd.Polar
