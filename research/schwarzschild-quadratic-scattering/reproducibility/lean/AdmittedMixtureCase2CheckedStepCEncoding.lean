import AdmittedMixtureCase2

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_c_checked_encoding : Expr.encode (NumeratorData.stepData 11 5 1 field).2.2 = Expr.encode stepC := by
  decide +kernel

#print axioms step_c_checked_encoding
end SchwarzschildMixtures.Case2
