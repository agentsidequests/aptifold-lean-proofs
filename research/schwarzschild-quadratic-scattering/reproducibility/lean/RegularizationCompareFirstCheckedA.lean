import RegularizationCompareFirst

namespace SchwarzschildMixtures.Regularization
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkedFirstA : Expr.Check comparisonFirst.1.1 comparisonFirst.2.1 := by
  decide +kernel

#print axioms checkedFirstA
end SchwarzschildMixtures.Regularization
