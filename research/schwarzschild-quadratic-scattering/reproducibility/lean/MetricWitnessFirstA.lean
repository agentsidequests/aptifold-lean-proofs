import MetricWitnessEvenReadout

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def firstA : Fraction := p2618
theorem firstA_reduced : Reduced MetricSourcePrograms.first.1 firstA := by
  have syntax_eq : MetricSourcePrograms.first.1 = f2618 := by
    simp only [MetricSourcePrograms.first, plus, Polar.coefficients, Polar.bareEvenRows,
      readout_syntax] <;> with_unfolding_all rfl
  rw [syntax_eq]
  exact h2618
#print axioms firstA_reduced
end SchwarzschildMixtures.MetricWitness
