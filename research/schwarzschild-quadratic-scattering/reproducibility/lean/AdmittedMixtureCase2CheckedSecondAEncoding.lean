import AdmittedMixtureCase2

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_a_checked_encoding : Expr.encode (NumeratorData.stepData 13 6 2 intermediate).1 = Expr.encode secondA := by
  decide +kernel

#print axioms second_a_checked_encoding
end SchwarzschildMixtures.Case2
