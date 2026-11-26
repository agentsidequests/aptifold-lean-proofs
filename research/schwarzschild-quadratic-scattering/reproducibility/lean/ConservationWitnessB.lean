import ConservationWitness021

namespace SchwarzschildMixtures.MixedConservationWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def valueB : Fraction := p733
theorem reducedB : Reduced Mixed.conservationCoefficients.2.1 valueB := by
  have syntax_eq : Mixed.conservationCoefficients.2.1 = f733 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact h733
theorem numeratorB : Expr.Check valueB.num (.constant 0) := by decide +kernel
#print axioms reducedB
#print axioms numeratorB

end SchwarzschildMixtures.MixedConservationWitness
