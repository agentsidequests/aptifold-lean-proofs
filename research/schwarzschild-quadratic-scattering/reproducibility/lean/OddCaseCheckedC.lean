import OddCase

namespace SchwarzschildMixtures.OddCase
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem odd_c_checked : Expr.Check (ArchivedOddData.restoredNumerators multiplier field).2.2 sourceC := by
  decide +kernel

#print axioms odd_c_checked
end SchwarzschildMixtures.OddCase
