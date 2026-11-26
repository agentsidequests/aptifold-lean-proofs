import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem polar_trace_checked : (polarCoordinateData.sphereTrace + -polarFormulaData.sphereTrace).num = [] := by
  decide +kernel

#print axioms polar_trace_checked
end SchwarzschildEinstein.PureOdd.Master
