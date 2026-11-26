import AdmittedMixtureCase2

namespace SchwarzschildMixtures.Case2
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_a_checked_bounds : let b := Expr.bounds (Expr.sub (NumeratorData.stepData 11 5 1 field).1 stepA)
  b.frequency < 16 ∧ b.angular < 64 ∧ b.mass < 2^112 := by
  decide +kernel

#print axioms step_a_checked_bounds
end SchwarzschildMixtures.Case2
