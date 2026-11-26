import MetricWitnessEvenReadout

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def differenceB : Fraction := p2883
theorem differenceB_reduced : Reduced MetricSourcePrograms.difference.2.1 differenceB := by
  have syntax_eq : MetricSourcePrograms.difference.2.1 = f2883 := by
    with_unfolding_all rfl
  rw [syntax_eq]
  exact h2883
#print axioms differenceB_reduced
end SchwarzschildMixtures.MetricWitness
