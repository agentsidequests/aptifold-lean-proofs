import MetricWitnessEvenReadout

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

def firstC : Fraction := p2860
theorem firstC_reduced : Reduced MetricSourcePrograms.first.2.2 firstC := by
  have syntax_eq : MetricSourcePrograms.first.2.2 = f2860 := by
    simp only [MetricSourcePrograms.first, plus, Polar.coefficients, Polar.bareEvenRows,
      readout_syntax] <;> with_unfolding_all rfl
  rw [syntax_eq]
  exact h2860
#print axioms firstC_reduced
end SchwarzschildMixtures.MetricWitness
