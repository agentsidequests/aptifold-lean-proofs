import MetricBareDifference

namespace SchwarzschildMixtures.MetricBareDifference
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_c_checked : Expr.Check (NumeratorData.stepData 11 5 1 field).2.2 stepC := by
  decide +kernel

#print axioms step_c_checked
end SchwarzschildMixtures.MetricBareDifference
