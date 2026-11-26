import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_c_checked_encoding : Expr.encode (NumeratorData.stepData 13 6 2 intermediate).2.2 = Expr.encode secondC := by
  decide +kernel

#print axioms second_c_checked_encoding
end SchwarzschildMixtures.Case1
