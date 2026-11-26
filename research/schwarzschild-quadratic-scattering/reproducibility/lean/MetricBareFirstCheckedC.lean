import MetricBareFirst

namespace SchwarzschildMixtures.MetricBareFirst
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_c_checked : Expr.Check (MetricBare.metricSecondStep field intermediate).2.2 sourceC := by
  decide +kernel

#print axioms source_c_checked
end SchwarzschildMixtures.MetricBareFirst
