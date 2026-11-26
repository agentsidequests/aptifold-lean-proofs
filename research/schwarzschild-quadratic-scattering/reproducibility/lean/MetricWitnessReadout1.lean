import MetricWitness072

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem rr_syntax : (Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular).rr = (f1098, f1430, f1736) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> with_unfolding_all rfl
#print axioms rr_syntax
end SchwarzschildMixtures.MetricWitness
