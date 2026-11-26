import AdmittedMixtureCase1

namespace SchwarzschildMixtures.Case1
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem source_a_checked_bounds : let b := Expr.bounds (Expr.sub (MetricBare.metricFinish field secondStep).1 sourceA)
  b.frequency < 16 ∧ b.angular < 64 ∧ b.mass < 2^112 := by
  decide +kernel

#print axioms source_a_checked_bounds
end SchwarzschildMixtures.Case1
