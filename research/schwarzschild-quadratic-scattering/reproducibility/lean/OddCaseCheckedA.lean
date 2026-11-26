import OddCase

namespace SchwarzschildMixtures.OddCase
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem odd_a_checked : Expr.Check (ArchivedOddData.restoredNumerators multiplier field).1 sourceA := by
  decide +kernel

#print axioms odd_a_checked
end SchwarzschildMixtures.OddCase
