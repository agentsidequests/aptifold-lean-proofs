import AdmittedMixtureCase1CheckedCBounds
import AdmittedMixtureCase1CheckedCEncoding

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_c_checked : Expr.Check (MetricBare.metricFinish field secondStep).2.2 sourceC := ⟨source_c_checked_bounds.1, source_c_checked_bounds.2.1, source_c_checked_bounds.2.2, source_c_checked_encoding⟩

#print axioms source_c_checked
end SchwarzschildMixtures.Case1
