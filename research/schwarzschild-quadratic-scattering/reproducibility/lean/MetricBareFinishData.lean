import MetricBareDenominatorData

namespace SchwarzschildMixtures.MetricBare

open NumeratorData

/-- Apply the daughter-potential term after the two derivative steps. -/
def metricFinish (field secondStep : ExprRow) : ExprRow :=
  subData secondStep (scaleData sparsePoles (scaleData sparsePoles (scaleData daughterData field)))

end SchwarzschildMixtures.MetricBare
