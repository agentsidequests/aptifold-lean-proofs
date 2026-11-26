import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem polar_radius_checked : (polarCoordinateData.rr + -polarFormulaData.rr).num = [] := by
  decide +kernel

#print axioms polar_radius_checked
end SchwarzschildEinstein.PureOdd.Master
