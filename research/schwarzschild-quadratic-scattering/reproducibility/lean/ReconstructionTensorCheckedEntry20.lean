import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_vt_checked : (angularCoordinateRicci 2 0 + -angularFormulaRicci 2 0).num = [] := by
  decide +kernel

#print axioms entry_vt_checked
end SchwarzschildEinstein.PureOdd.Master
