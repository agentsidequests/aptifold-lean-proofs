import ReconstructionTensorPart2Divergence
import ReconstructionTensorPart2Left
import ReconstructionTensorPart2Right

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_vv_checked : (angularCoordinateRicci 2 2 + -angularFormulaRicci 2 2).num = [] := by
  simp only [angularCoordinateRicci, ricci_v_divergence, ricci_v_left, ricci_v_right]
  decide +kernel

#print axioms entry_vv_checked
end SchwarzschildEinstein.PureOdd.Master
