import ReconstructionTensorPart1Divergence
import ReconstructionTensorPart1Left
import ReconstructionTensorPart1Right

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_rr_checked : (angularCoordinateRicci 1 1 + -angularFormulaRicci 1 1).num = [] := by
  simp only [angularCoordinateRicci, ricci_r_divergence, ricci_r_left, ricci_r_right]
  decide +kernel

#print axioms entry_rr_checked
end SchwarzschildEinstein.PureOdd.Master
