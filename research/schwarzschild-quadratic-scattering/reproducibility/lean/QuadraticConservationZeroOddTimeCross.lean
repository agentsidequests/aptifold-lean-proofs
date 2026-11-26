import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddTimeCross : Vacuum.zeroCertificate (conservationProgram false).1.2.1 := by
  have syntax_eq : (conservationProgram false).1.2.1 = f2488 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2488, h2488, by decide +kernel⟩
#print axioms zeroOddTimeCross

end SchwarzschildEinstein.PureOdd.Master
