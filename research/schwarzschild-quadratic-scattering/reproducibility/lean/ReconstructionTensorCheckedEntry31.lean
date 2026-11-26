import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_qr_checked : (angularCoordinateRicci 3 1 + -angularFormulaRicci 3 1).num = [] := by
  decide +kernel

#print axioms entry_qr_checked
end SchwarzschildEinstein.PureOdd.Master
