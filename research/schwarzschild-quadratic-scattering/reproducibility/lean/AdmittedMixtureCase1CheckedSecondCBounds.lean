import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem second_c_checked_bounds : let b := Expr.bounds (Expr.sub (NumeratorData.stepData 13 6 2 intermediate).2.2 secondC)
  b.frequency < 16 ∧ b.angular < 64 ∧ b.mass < 2^112 := by
  decide +kernel

#print axioms second_c_checked_bounds
end SchwarzschildMixtures.Case1
