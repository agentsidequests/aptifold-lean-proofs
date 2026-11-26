import AdmittedMixtureCase2

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_a_checked_encoding : Expr.encode (MetricBare.metricFinish field secondStep).1 = Expr.encode sourceA := by
  decide +kernel

#print axioms source_a_checked_encoding
end SchwarzschildMixtures.Case2
