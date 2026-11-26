import MetricBareDifference

namespace SchwarzschildMixtures.MetricBareDifference
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_b_checked : Expr.Check (MetricBare.metricFinish field secondStep).2.1 sourceB := by
  decide +kernel

#print axioms source_b_checked
end SchwarzschildMixtures.MetricBareDifference
