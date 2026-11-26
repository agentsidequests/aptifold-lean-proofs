import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_rq_checked : (angularCoordinateRicci 1 3 + -angularFormulaRicci 1 3).num = [] := by
  decide +kernel

#print axioms entry_rq_checked
end SchwarzschildEinstein.PureOdd.Master
