import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem polar_tracefree_checked : (polarCoordinateData.traceFree + -polarFormulaData.traceFree).num = [] := by
  decide +kernel

#print axioms polar_tracefree_checked
end SchwarzschildEinstein.PureOdd.Master
