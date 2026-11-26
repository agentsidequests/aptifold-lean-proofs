import RegularizationCompareOdd

namespace SchwarzschildMixtures.Regularization
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkedOddC : Expr.Check comparisonOdd.1.2.2 comparisonOdd.2.2.2 := by
  decide +kernel

#print axioms checkedOddC
end SchwarzschildMixtures.Regularization
