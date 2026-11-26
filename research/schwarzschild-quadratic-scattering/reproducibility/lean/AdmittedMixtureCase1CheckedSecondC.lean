import AdmittedMixtureCase1CheckedSecondCBounds
import AdmittedMixtureCase1CheckedSecondCEncoding

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_c_checked : Expr.Check (NumeratorData.stepData 13 6 2 intermediate).2.2 secondC := ⟨second_c_checked_bounds.1, second_c_checked_bounds.2.1, second_c_checked_bounds.2.2, second_c_checked_encoding⟩

#print axioms second_c_checked
end SchwarzschildMixtures.Case1
