import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_qv_checked : (angularCoordinateRicci 3 2 + -angularFormulaRicci 3 2).num = [] := by
  decide +kernel

#print axioms entry_qv_checked
end SchwarzschildEinstein.PureOdd.Master
