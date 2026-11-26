import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_qt_checked : (angularCoordinateRicci 3 0 + -angularFormulaRicci 3 0).num = [] := by
  decide +kernel

#print axioms entry_qt_checked
end SchwarzschildEinstein.PureOdd.Master
