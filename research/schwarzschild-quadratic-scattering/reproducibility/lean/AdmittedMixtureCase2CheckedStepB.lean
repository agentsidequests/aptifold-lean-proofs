import AdmittedMixtureCase2CheckedStepBBounds
import AdmittedMixtureCase2CheckedStepBEncoding

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_b_checked : Expr.Check (NumeratorData.stepData 11 5 1 field).2.1 stepB := ⟨step_b_checked_bounds.1, step_b_checked_bounds.2.1, step_b_checked_bounds.2.2, step_b_checked_encoding⟩

#print axioms step_b_checked
end SchwarzschildMixtures.Case2
