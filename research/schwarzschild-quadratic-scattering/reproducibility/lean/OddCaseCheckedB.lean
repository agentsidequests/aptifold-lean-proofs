import OddCase

namespace SchwarzschildMixtures.OddCase
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem odd_b_checked : Expr.Check (ArchivedOddData.restoredNumerators multiplier field).2.1 sourceB := by
  decide +kernel

#print axioms odd_b_checked
end SchwarzschildMixtures.OddCase
