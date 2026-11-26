import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_vq_checked : (angularCoordinateRicci 2 3 + -angularFormulaRicci 2 3).num = [] := by
  decide +kernel

#print axioms entry_vq_checked
end SchwarzschildEinstein.PureOdd.Master
