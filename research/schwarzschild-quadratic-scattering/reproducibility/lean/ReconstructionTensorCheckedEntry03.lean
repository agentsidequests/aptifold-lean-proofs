import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_tq_checked : (angularCoordinateRicci 0 3 + -angularFormulaRicci 0 3).num = [] := by
  decide +kernel

#print axioms entry_tq_checked
end SchwarzschildEinstein.PureOdd.Master
