import RegularizationCompareSecond

namespace SchwarzschildMixtures.Regularization
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkedSecondC : Expr.Check comparisonSecond.1.2.2 comparisonSecond.2.2.2 := by
  decide +kernel

#print axioms checkedSecondC
end SchwarzschildMixtures.Regularization
