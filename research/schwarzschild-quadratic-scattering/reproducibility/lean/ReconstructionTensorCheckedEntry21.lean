import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_vr_checked : (angularCoordinateRicci 2 1 + -angularFormulaRicci 2 1).num = [] := by
  decide +kernel

#print axioms entry_vr_checked
end SchwarzschildEinstein.PureOdd.Master
