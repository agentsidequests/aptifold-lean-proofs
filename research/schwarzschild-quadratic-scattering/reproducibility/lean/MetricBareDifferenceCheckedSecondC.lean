import MetricBareDifference

namespace SchwarzschildMixtures.MetricBareDifference
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_c_checked : Expr.Check (NumeratorData.stepData 13 6 2 intermediate).2.2 secondC := by
  decide +kernel

#print axioms second_c_checked
end SchwarzschildMixtures.MetricBareDifference
