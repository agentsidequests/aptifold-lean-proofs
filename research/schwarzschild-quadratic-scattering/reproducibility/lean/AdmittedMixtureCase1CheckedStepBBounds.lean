import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_b_checked_bounds : let b := Expr.bounds (Expr.sub (NumeratorData.stepData 11 5 1 field).2.1 stepB)
  b.frequency < 16 ∧ b.angular < 64 ∧ b.mass < 2^112 := by
  decide +kernel

#print axioms step_b_checked_bounds
end SchwarzschildMixtures.Case1
