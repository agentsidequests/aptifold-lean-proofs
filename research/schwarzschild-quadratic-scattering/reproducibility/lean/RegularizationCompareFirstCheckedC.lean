import RegularizationCompareFirst

namespace SchwarzschildMixtures.Regularization
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkedFirstC : Expr.Check comparisonFirst.1.2.2 comparisonFirst.2.2.2 := by
  decide +kernel

#print axioms checkedFirstC
end SchwarzschildMixtures.Regularization
