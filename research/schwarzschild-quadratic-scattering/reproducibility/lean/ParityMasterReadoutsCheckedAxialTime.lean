import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem axial_time_checked : (axialCoordinateData.time + -axialFormulaData.time).num = [] := by
  decide +kernel

#print axioms axial_time_checked
end SchwarzschildEinstein.PureOdd.Master
