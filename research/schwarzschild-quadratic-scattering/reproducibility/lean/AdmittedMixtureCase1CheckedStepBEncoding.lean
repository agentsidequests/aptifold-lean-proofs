import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_b_checked_encoding : Expr.encode (NumeratorData.stepData 11 5 1 field).2.1 = Expr.encode stepB := by
  decide +kernel

#print axioms step_b_checked_encoding
end SchwarzschildMixtures.Case1
