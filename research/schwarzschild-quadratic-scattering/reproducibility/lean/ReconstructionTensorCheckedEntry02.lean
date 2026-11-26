import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_tv_checked : (angularCoordinateRicci 0 2 + -angularFormulaRicci 0 2).num = [] := by
  decide +kernel

#print axioms entry_tv_checked
end SchwarzschildEinstein.PureOdd.Master
