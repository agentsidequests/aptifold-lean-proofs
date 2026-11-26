import RegularizationCompareSecond

namespace SchwarzschildMixtures.Regularization
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkedSecondA : Expr.Check comparisonSecond.1.1 comparisonSecond.2.1 := by
  decide +kernel

#print axioms checkedSecondA
end SchwarzschildMixtures.Regularization
