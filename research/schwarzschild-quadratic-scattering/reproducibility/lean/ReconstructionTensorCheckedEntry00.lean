import ReconstructionTensorPart0Divergence
import ReconstructionTensorPart0Left
import ReconstructionTensorPart0Right

namespace SchwarzschildEinstein.PureOdd.Master
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem entry_tt_checked : (angularCoordinateRicci 0 0 + -angularFormulaRicci 0 0).num = [] := by
  simp only [angularCoordinateRicci, ricci_t_divergence, ricci_t_left, ricci_t_right]
  decide +kernel

#print axioms entry_tt_checked
end SchwarzschildEinstein.PureOdd.Master
