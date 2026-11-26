import ConservationWitness021

namespace SchwarzschildMixtures.MixedConservationWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def valueC : Fraction := p742
theorem reducedC : Reduced Mixed.conservationCoefficients.2.2 valueC := by
  have syntax_eq : Mixed.conservationCoefficients.2.2 = f742 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact h742
theorem numeratorC : Expr.Check valueC.num (.constant 0) := by decide +kernel
#print axioms reducedC
#print axioms numeratorC

end SchwarzschildMixtures.MixedConservationWitness
