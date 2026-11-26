import AdmittedMixtureCase2CheckedSecondBBounds
import AdmittedMixtureCase2CheckedSecondBEncoding

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_b_checked : Expr.Check (NumeratorData.stepData 13 6 2 intermediate).2.1 secondB := ⟨second_b_checked_bounds.1, second_b_checked_bounds.2.1, second_b_checked_bounds.2.2, second_b_checked_encoding⟩

#print axioms second_b_checked
end SchwarzschildMixtures.Case2
