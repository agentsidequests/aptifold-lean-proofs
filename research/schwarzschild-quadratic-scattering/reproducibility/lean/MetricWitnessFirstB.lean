import MetricWitnessEvenReadout

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def firstB : Fraction := p2830
theorem firstB_reduced : Reduced MetricSourcePrograms.first.2.1 firstB := by
  have syntax_eq : MetricSourcePrograms.first.2.1 = f2830 := by
    simp only [MetricSourcePrograms.first, plus, Polar.coefficients, Polar.bareEvenRows,
      readout_syntax] <;> with_unfolding_all rfl
  rw [syntax_eq]
  exact h2830
#print axioms firstB_reduced
end SchwarzschildMixtures.MetricWitness
