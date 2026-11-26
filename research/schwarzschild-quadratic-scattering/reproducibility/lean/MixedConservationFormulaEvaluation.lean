import MixedConservationRows
import MixedFormulaEvaluation

/-! Interpret the conservation program in the same field as the mixed tensor. -/
namespace SchwarzschildEinstein.PureOdd.Mixed

open SchwarzschildMixtures.ExactRational SchwarzschildMixtures.PureOddProgram

noncomputable section

variable {K : Type} [DivisionRing K]
variable (d : K → K) (radius frequency angular : K)

local notation "F" => Formula.interpret d radius frequency angular
local notation "L" => mapLinear F
local notation "Q" => mapRow F

private theorem eval_angular_sample (r w e : Formula)
    (T P : RadialJet (Linear Formula)) (E : PolarParentJets (Linear Formula))
    (f : Linear Formula → Formula) (g : Linear K → K)
    (select : ∀ v, F (f v) = g (L v)) :
    F (evaluateAngular rationalConstant r w e T P E f) =
      evaluateAngular (fun q => (q : K)) (F r) (F w) (F e)
        (mapJet L T) (mapJet L P) (mapPolarJets L E) g := by
  dsimp only [evaluateAngular, angularRicciCoefficient, mapJet, mapPolarJets]
  simp only [Formula.interpret_add, Formula.interpret_neg, Formula.interpret_mul,
    Formula.interpret_div, Formula.interpret_sub, eval_rat, select, lapse]
  simp only [OfNat.ofNat]
  eval_mixed_formula

private theorem eval_angular_interpolation (r w e : Formula)
    (T P : RadialJet (Linear Formula)) (E : PolarParentJets (Linear Formula)) :
    Q (interpolateAngular rationalConstant r w e T P E) =
      interpolateAngular (fun q => (q : K)) (F r) (F w) (F e)
        (mapJet L T) (mapJet L P) (mapPolarJets L E) := by
  simp only [interpolateAngular, recoverRow, mapRow, Formula.interpret_sub,
    eval_angular_sample d radius frequency angular r w e T P E Prod.fst Prod.fst (fun _ => rfl),
    eval_angular_sample d radius frequency angular r w e T P E
      (fun p => p.1+p.2) (fun p => p.1+p.2) (fun _ => rfl),
    eval_angular_sample d radius frequency angular r w e T P E Prod.snd Prod.snd (fun _ => rfl)]

private theorem eval_reconstructed_angular (r w e : Formula) :
    Q (reconstructedAngular rationalConstant Formula.dr r w e) =
      reconstructedAngular (fun q => (q : K)) d (F r) (F w) (F e) := by
  simpa only [reconstructedAngular, eval_parent_jet, eval_time_amplitude, eval_radius_amplitude,
    eval_polar] using eval_angular_interpolation d radius frequency angular r w e
      (parentJet Formula.dr r w e (timeAmplitude r))
      (parentJet Formula.dr r w e (radiusAmplitude r w))
      (polarReconstruction Formula.dr r w e)

theorem conservation_program_value :
    Q conservationCoefficients = conservationRows (fun q => (q : K)) d radius frequency angular := by
  obtain ⟨t,p⟩ := eval_reconstructed d radius frequency angular .radius .frequency .angular
  have hr : F .radius = radius := rfl
  have hw : F .frequency = frequency := rfl
  have he : F .angular = angular := rfl
  simp only [conservationCoefficients, conservationRows, eval_plus, eval_scale, eval_quadratic_derivative,
    eval_reconstructed_angular, t, p, lapse, hr, hw, he]
  simp only [OfNat.ofNat]
  eval_mixed_formula

#print axioms conservation_program_value

end
end SchwarzschildEinstein.PureOdd.Mixed
