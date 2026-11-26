import AdmittedMixtureCase2

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_b_checked_encoding : Expr.encode (MetricBare.metricFinish field secondStep).2.1 = Expr.encode sourceB := by
  decide +kernel

#print axioms source_b_checked_encoding
end SchwarzschildMixtures.Case2
