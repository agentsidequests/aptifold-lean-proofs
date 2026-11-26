import AdmittedMixtureCase2CheckedSecondABounds
import AdmittedMixtureCase2CheckedSecondAEncoding

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_a_checked : Expr.Check (NumeratorData.stepData 13 6 2 intermediate).1 secondA := ⟨second_a_checked_bounds.1, second_a_checked_bounds.2.1, second_a_checked_bounds.2.2, second_a_checked_encoding⟩

#print axioms second_a_checked
end SchwarzschildMixtures.Case2
