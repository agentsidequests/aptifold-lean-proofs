import RegularizationCompareOdd

namespace SchwarzschildMixtures.Regularization
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkedOddA : Expr.Check comparisonOdd.1.1 comparisonOdd.2.1 := by
  decide +kernel

#print axioms checkedOddA
end SchwarzschildMixtures.Regularization
