import MetricWitnessEvenReadout

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def differenceA : Fraction := p2881
theorem differenceA_reduced : Reduced MetricSourcePrograms.difference.1 differenceA := by
  have syntax_eq : MetricSourcePrograms.difference.1 = f2881 := by
    with_unfolding_all rfl
  rw [syntax_eq]
  exact h2881
#print axioms differenceA_reduced
end SchwarzschildMixtures.MetricWitness
