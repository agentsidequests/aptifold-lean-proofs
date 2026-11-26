import RegularizationRegulators
import AdmittedMixtureCase1
import MetricBareFirst

namespace SchwarzschildMixtures.Regularization

def comparisonFirst : ExprRow × ExprRow :=
  baseComparison Case1.field MetricBareFirst.field (addData evenEven (addData evenOdd oddOdd))
    Case1.multiplier MetricBareFirst.multiplier regulatorMultiplier

end SchwarzschildMixtures.Regularization
