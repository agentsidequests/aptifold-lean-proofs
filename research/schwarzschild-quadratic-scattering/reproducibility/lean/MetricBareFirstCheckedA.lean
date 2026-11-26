import MetricBareFirst

namespace SchwarzschildMixtures.MetricBareFirst
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_a_checked : Expr.Check (MetricBare.metricSecondStep field intermediate).1 sourceA := by
  decide +kernel

#print axioms source_a_checked
end SchwarzschildMixtures.MetricBareFirst
