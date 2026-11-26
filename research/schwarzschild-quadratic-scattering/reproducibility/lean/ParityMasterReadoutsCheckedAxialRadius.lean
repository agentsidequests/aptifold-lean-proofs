import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem axial_radius_checked : (axialCoordinateData.radius + -axialFormulaData.radius).num = [] := by
  decide +kernel

#print axioms axial_radius_checked
end SchwarzschildEinstein.PureOdd.Master
