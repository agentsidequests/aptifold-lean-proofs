import RegularizationRegulators
import OddCase
import OddBareCase

namespace SchwarzschildMixtures.Regularization

def comparisonOdd : ExprRow × ExprRow :=
  baseComparison OddCase.field OddBareCase.field oddOdd
    (OddCase.multiplier * SchwarzschildMatrix.sourceScale.toNat)
    (OddBareCase.multiplier * SchwarzschildMatrix.sourceScale.toNat) regulatorMultiplier

end SchwarzschildMixtures.Regularization
