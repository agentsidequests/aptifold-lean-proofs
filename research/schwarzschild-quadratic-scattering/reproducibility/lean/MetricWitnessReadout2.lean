import MetricWitness072

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem radialVector_syntax : (Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular).radialVector = (f299, f1495, f2656) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> with_unfolding_all rfl
#print axioms radialVector_syntax
end SchwarzschildMixtures.MetricWitness
