import MetricBareDifference

namespace SchwarzschildMixtures.MetricBareDifference
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_a_checked : Expr.Check (NumeratorData.stepData 13 6 2 intermediate).1 secondA := by
  decide +kernel

#print axioms second_a_checked
end SchwarzschildMixtures.MetricBareDifference
