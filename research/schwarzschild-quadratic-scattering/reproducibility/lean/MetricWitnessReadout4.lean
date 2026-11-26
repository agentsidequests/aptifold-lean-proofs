import MetricWitness072

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem traceFree_syntax : (Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular).traceFree = (f708, f1498, f2659) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> with_unfolding_all rfl
#print axioms traceFree_syntax
end SchwarzschildMixtures.MetricWitness
