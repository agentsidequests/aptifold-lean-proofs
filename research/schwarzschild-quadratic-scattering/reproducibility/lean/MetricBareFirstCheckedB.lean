import MetricBareFirst

namespace SchwarzschildMixtures.MetricBareFirst
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_b_checked : Expr.Check (MetricBare.metricSecondStep field intermediate).2.1 sourceB := by
  decide +kernel

#print axioms source_b_checked
end SchwarzschildMixtures.MetricBareFirst
