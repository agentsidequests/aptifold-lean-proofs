import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_tr_checked : (angularCoordinateRicci 0 1 + -angularFormulaRicci 0 1).num = [] := by
  decide +kernel

#print axioms entry_tr_checked
end SchwarzschildEinstein.PureOdd.Master
