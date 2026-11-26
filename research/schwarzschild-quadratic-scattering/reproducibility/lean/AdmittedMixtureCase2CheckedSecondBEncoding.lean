import AdmittedMixtureCase2

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_b_checked_encoding : Expr.encode (NumeratorData.stepData 13 6 2 intermediate).2.1 = Expr.encode secondB := by
  decide +kernel

#print axioms second_b_checked_encoding
end SchwarzschildMixtures.Case2
