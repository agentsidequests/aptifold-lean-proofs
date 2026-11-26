import ConservationWitness021

namespace SchwarzschildMixtures.MixedConservationWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def valueA : Fraction := p719
theorem reducedA : Reduced Mixed.conservationCoefficients.1 valueA := by
  have syntax_eq : Mixed.conservationCoefficients.1 = f719 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact h719
theorem numeratorA : Expr.Check valueA.num (.constant 0) := by decide +kernel
#print axioms reducedA
#print axioms numeratorA

end SchwarzschildMixtures.MixedConservationWitness
