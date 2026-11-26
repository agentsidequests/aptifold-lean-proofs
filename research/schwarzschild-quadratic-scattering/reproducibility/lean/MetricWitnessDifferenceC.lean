import MetricWitnessEvenReadout

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def differenceC : Fraction := p2885
theorem differenceC_reduced : Reduced MetricSourcePrograms.difference.2.2 differenceC := by
  have syntax_eq : MetricSourcePrograms.difference.2.2 = f2885 := by
    with_unfolding_all rfl
  rw [syntax_eq]
  exact h2885
#print axioms differenceC_reduced
end SchwarzschildMixtures.MetricWitness
