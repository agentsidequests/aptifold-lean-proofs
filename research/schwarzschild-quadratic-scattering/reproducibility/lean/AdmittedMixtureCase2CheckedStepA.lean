import AdmittedMixtureCase2CheckedStepABounds
import AdmittedMixtureCase2CheckedStepAEncoding

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_a_checked : Expr.Check (NumeratorData.stepData 11 5 1 field).1 stepA := ⟨step_a_checked_bounds.1, step_a_checked_bounds.2.1, step_a_checked_bounds.2.2, step_a_checked_encoding⟩

#print axioms step_a_checked
end SchwarzschildMixtures.Case2
