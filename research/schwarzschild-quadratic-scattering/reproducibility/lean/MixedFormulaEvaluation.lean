import MixedProgram
import PureOddFormulaEvaluation
import Mathlib.Data.Rat.Cast.Defs

/-! Evaluate the exported expressions as exactly the same formulas
that occur in the mixed curvature and radial master proof. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open SchwarzschildMixtures.ExactRational SchwarzschildMixtures.PureOddProgram

noncomputable section

variable {K : Type} [DivisionRing K]
variable (d : K → K) (radius frequency angular : K)

local notation "F" => Formula.interpret d radius frequency angular
local notation "L" => mapLinear F
local notation "Q" => mapRow F

macro "eval_mixed_formula" : tactic =>
  `(tactic|
    ((try (simp only [Formula.interpret_add, Formula.interpret_sub, Formula.interpret_neg,
      Formula.interpret_mul, Formula.interpret_div, Formula.interpret_pow, Formula.interpret_dr]))
     <;> (try (simp only [instOfNat_pureOddFormulas, instOfNat_mixedRadialFormulas, OfNat.ofNat,
       Formula.interpret]))
     <;> (try (simp only [Int.cast_natCast, Int.cast_one, Nat.cast_one]))
     <;> rfl))

theorem eval_rat (q : Rat) :
    F (rationalConstant q) = (q : K) := by
  unfold rationalConstant
  split
  · rename_i unit
    have value := (Rat.den_eq_one_iff q).mp unit
    exact (Rat.cast_intCast q.num).symm.trans (congrArg (fun t : Rat => (t : K)) value)
  · rw [Rat.cast_def]
    simp only [Formula.interpret, Int.cast_natCast]

private theorem eval_linearAdd (u v : Linear Formula) :
    L (linearAdd u v) = linearAdd (L u) (L v) := rfl

private theorem eval_linearScale (a : Formula) (u : Linear Formula) :
    L (linearScale a u) = linearScale (F a) (L u) := rfl

private theorem eval_even_amplitude (r w e : Formula) :
    L (evenParentAmplitude r w e) = evenParentAmplitude (F r) (F w) (F e) := by
  simp only [mapLinear, evenParentAmplitude, parentSuperpotential, parentAlgebraicFrequency,
    halfAngularEigenvalue, lapse]
  eval_mixed_formula

private theorem eval_sphere_coefficient (r e : Formula) :
    F (evenSphereCoefficient r e) = evenSphereCoefficient (F r) (F e) := by
  simp only [evenSphereCoefficient, halfAngularEigenvalue]
  eval_mixed_formula

private theorem eval_cross_coefficient (r e : Formula) :
    F (evenCrossCoefficient r e) = evenCrossCoefficient (F r) (F e) := by
  simp only [evenCrossCoefficient, halfAngularEigenvalue, lapse]
  eval_mixed_formula

theorem eval_polar (r w e : Formula) :
    mapPolarJets L (polarReconstruction Formula.dr r w e) =
      polarReconstruction d (F r) (F w) (F e) := by
  simp only [mapPolarJets, polarReconstruction, eval_parent_jet, eval_linearAdd, eval_linearScale,
    eval_linear_derivative, eval_even_amplitude, eval_sphere_coefficient, eval_cross_coefficient, lapse]
  eval_mixed_formula

private theorem eval_component (r w e : Formula)
    (T P : RadialJet (Linear Formula)) (B : PolarParentJets (Linear Formula))
    (f : Linear Formula → Formula) (g : Linear K → K)
    (select : ∀ q, F (f q) = g (L q)) :
    let a := evaluateVector rationalConstant r w e T P B f
    let b := evaluateVector (fun q => (q : K)) (F r) (F w) (F e)
      (mapJet L T) (mapJet L P) (mapPolarJets L B) g
    F a.time = b.time ∧ F a.radius = b.radius := by
  dsimp only [evaluateVector, vectorCoefficients, mapJet, mapPolarJets]
  simp only [Formula.interpret_add, Formula.interpret_neg, Formula.interpret_mul,
    Formula.interpret_div, Formula.interpret_sub, eval_rat, select, lapse]
  constructor <;> eval_mixed_formula

private theorem eval_interpolation (r w e : Formula)
    (T P : RadialJet (Linear Formula)) (B : PolarParentJets (Linear Formula)) :
    let a := interpolateVector rationalConstant r w e T P B
    let b := interpolateVector (fun q => (q : K)) (F r) (F w) (F e)
      (mapJet L T) (mapJet L P) (mapPolarJets L B)
    Q a.time = b.time ∧ Q a.radius = b.radius := by
  have first := eval_component d radius frequency angular r w e T P B Prod.fst Prod.fst
    (fun _ => rfl)
  have sum := eval_component d radius frequency angular r w e T P B
    (fun q => q.1+q.2) (fun q => q.1+q.2) (fun _ => rfl)
  have last := eval_component d radius frequency angular r w e T P B Prod.snd Prod.snd
    (fun _ => rfl)
  dsimp only at first sum last ⊢
  simp only [interpolateVector, recoverRow, mapRow, Formula.interpret_sub,
    first.1, first.2, sum.1, sum.2, last.1, last.2, and_self]

theorem eval_reconstructed (r w e : Formula) :
    let a := reconstructedVector rationalConstant Formula.dr r w e
    let b := reconstructedVector (fun q => (q : K)) d (F r) (F w) (F e)
    Q a.time = b.time ∧ Q a.radius = b.radius := by
  simp only [reconstructedVector]
  have check := eval_interpolation d radius frequency angular r w e
    (parentJet Formula.dr r w e (timeAmplitude r))
    (parentJet Formula.dr r w e (radiusAmplitude r w)) (polarReconstruction Formula.dr r w e)
  simpa only [eval_parent_jet, eval_time_amplitude, eval_radius_amplitude, eval_polar] using check

theorem mixed_program_value :
    Q Mixed.coefficients = bareMixedRows (fun q => (q : K)) d radius frequency angular := by
  obtain ⟨t,p⟩ := eval_reconstructed d radius frequency angular .radius .frequency .angular
  have hr : F .radius = radius := rfl
  have hw : F .frequency = frequency := rfl
  have he : F .angular = angular := rfl
  simp only [Mixed.coefficients, bareMixedRows, eval_scale, eval_plus, eval_quadratic_derivative,
    t, p, oddMasterScale, lapse, hr, hw, he]
  eval_mixed_formula

#print axioms mixed_program_value

end
end SchwarzschildEinstein.PureOdd.Mixed
