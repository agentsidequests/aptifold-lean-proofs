import MetricWitness072

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem tt_syntax : (Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular).tt = (f1108, f1426, f1732) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> with_unfolding_all rfl
#print axioms tt_syntax
end SchwarzschildMixtures.MetricWitness
