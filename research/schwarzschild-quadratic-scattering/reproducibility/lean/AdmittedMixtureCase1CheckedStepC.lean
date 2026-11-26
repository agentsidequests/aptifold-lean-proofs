import AdmittedMixtureCase1CheckedStepCBounds
import AdmittedMixtureCase1CheckedStepCEncoding

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_c_checked : Expr.Check (NumeratorData.stepData 11 5 1 field).2.2 stepC := ⟨step_c_checked_bounds.1, step_c_checked_bounds.2.1, step_c_checked_bounds.2.2, step_c_checked_encoding⟩

#print axioms step_c_checked
end SchwarzschildMixtures.Case1
