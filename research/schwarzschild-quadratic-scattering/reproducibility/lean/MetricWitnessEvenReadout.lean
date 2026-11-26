import MetricWitnessReadout0
import MetricWitnessReadout1
import MetricWitnessReadout2
import MetricWitnessReadout3
import MetricWitnessReadout4

namespace SchwarzschildMixtures.MetricWitness
open ExactRational SchwarzschildEinstein.PureOdd
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem readout_syntax : Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular = ⟨(f1108, f1426, f1732), (f1098, f1430, f1736), (f299, f1495, f2656), (f1441, f1746, f2671), (f708, f1498, f2659)⟩ := by
  let s := Polar.evenSourceRows Mixed.rationalConstant Formula.dr .radius .frequency .angular
  have eta : s = ⟨s.tt, s.rr, s.radialVector, s.sphereTrace, s.traceFree⟩ := by cases s <;> rfl
  calc
    s = ⟨s.tt, s.rr, s.radialVector, s.sphereTrace, s.traceFree⟩ := eta
    _ = _ := by simp only [s, tt_syntax, rr_syntax, radialVector_syntax, sphereTrace_syntax, traceFree_syntax]
#print axioms readout_syntax
end SchwarzschildMixtures.MetricWitness
