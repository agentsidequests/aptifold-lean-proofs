import MetricBareDifference

namespace SchwarzschildMixtures.MetricBareDifference
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_a_checked : Expr.Check (NumeratorData.stepData 11 5 1 field).1 stepA := by
  decide +kernel

#print axioms step_a_checked
end SchwarzschildMixtures.MetricBareDifference
