import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddRadiusCross : Vacuum.zeroCertificate (conservationProgram false).2.1.2.1 := by
  have syntax_eq : (conservationProgram false).2.1.2.1 = f2833 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2833, h2833, by decide +kernel⟩
#print axioms zeroOddRadiusCross

end SchwarzschildEinstein.PureOdd.Master
