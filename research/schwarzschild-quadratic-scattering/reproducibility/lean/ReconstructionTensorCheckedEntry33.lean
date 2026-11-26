import ReconstructionTensorPart3Divergence
import ReconstructionTensorPart3Left
import ReconstructionTensorPart3Right

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_qq_checked : (angularCoordinateRicci 3 3 + -angularFormulaRicci 3 3).num = [] := by
  simp only [angularCoordinateRicci, ricci_q_divergence, ricci_q_left, ricci_q_right]
  decide +kernel

#print axioms entry_qq_checked
end SchwarzschildEinstein.PureOdd.Master
