import MetricWitness072

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem sphereTrace_syntax : (Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular).sphereTrace = (f1441, f1746, f2671) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> with_unfolding_all rfl
#print axioms sphereTrace_syntax
end SchwarzschildMixtures.MetricWitness
