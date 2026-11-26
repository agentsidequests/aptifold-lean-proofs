import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem horizon_checked : Expr.Check (horizonData field) (Expr.constant 0) := by
  decide +kernel

#print axioms horizon_checked
end SchwarzschildMixtures.Case1
