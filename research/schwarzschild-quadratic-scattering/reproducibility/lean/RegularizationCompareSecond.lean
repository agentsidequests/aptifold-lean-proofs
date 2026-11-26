import RegularizationRegulators
import AdmittedMixtureCase2
import MetricBareFirst
import MetricBareDifference

namespace SchwarzschildMixtures.Regularization

def comparisonSecond : ExprRow × ExprRow :=
  secondComparison Case2.field MetricBareFirst.field MetricBareDifference.field evenEven evenOdd oddOdd
    Case2.multiplier MetricBareFirst.multiplier MetricBareDifference.multiplier regulatorMultiplier

end SchwarzschildMixtures.Regularization
