import AdmittedMixtureCase2CheckedABounds
import AdmittedMixtureCase2CheckedAEncoding

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_a_checked : Expr.Check (MetricBare.metricFinish field secondStep).1 sourceA := ⟨source_a_checked_bounds.1, source_a_checked_bounds.2.1, source_a_checked_bounds.2.2, source_a_checked_encoding⟩

#print axioms source_a_checked
end SchwarzschildMixtures.Case2
