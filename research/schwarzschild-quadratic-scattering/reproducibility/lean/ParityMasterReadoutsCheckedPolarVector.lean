import ParityMasterReadouts

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem polar_vector_checked : (polarCoordinateData.radialVector + -polarFormulaData.radialVector).num = [] := by
  decide +kernel

#print axioms polar_vector_checked
end SchwarzschildEinstein.PureOdd.Master
