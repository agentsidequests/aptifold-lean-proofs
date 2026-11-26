import ParityReconstructionAngular

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_rt_checked : (angularCoordinateRicci 1 0 + -angularFormulaRicci 1 0).num = [] := by
  decide +kernel

#print axioms entry_rt_checked
end SchwarzschildEinstein.PureOdd.Master
