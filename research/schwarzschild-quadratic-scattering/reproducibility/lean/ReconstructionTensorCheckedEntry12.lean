import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_rv_checked : (angularCoordinateRicci 1 2 + -angularFormulaRicci 1 2).num = [] := by
  decide +kernel

#print axioms entry_rv_checked
end SchwarzschildEinstein.PureOdd.Master
