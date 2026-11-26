import MetricBareDifference

namespace SchwarzschildMixtures.MetricBareDifference
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_b_checked : Expr.Check (NumeratorData.stepData 11 5 1 field).2.1 stepB := by
  decide +kernel

#print axioms step_b_checked
end SchwarzschildMixtures.MetricBareDifference
