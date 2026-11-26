import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem polar_time_checked : (polarCoordinateData.tt + -polarFormulaData.tt).num = [] := by
  decide +kernel

#print axioms polar_time_checked
end SchwarzschildEinstein.PureOdd.Master
