import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_c_checked_encoding : Expr.encode (MetricBare.metricFinish field secondStep).2.2 = Expr.encode sourceC := by
  decide +kernel

#print axioms source_c_checked_encoding
end SchwarzschildMixtures.Case1
