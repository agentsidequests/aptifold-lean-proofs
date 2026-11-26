import AdmittedMixtureCase1CheckedBBounds
import AdmittedMixtureCase1CheckedBEncoding

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_b_checked : Expr.Check (MetricBare.metricFinish field secondStep).2.1 sourceB := ⟨source_b_checked_bounds.1, source_b_checked_bounds.2.1, source_b_checked_bounds.2.2, source_b_checked_encoding⟩

#print axioms source_b_checked
end SchwarzschildMixtures.Case1
