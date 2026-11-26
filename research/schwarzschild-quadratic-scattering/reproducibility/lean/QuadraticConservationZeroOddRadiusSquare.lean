import QuadraticConservationArithmetic073
import VacuumRadialData

namespace SchwarzschildEinstein.PureOdd.Master
open SchwarzschildMixtures SchwarzschildMixtures.ExactRational
set_option maxRecDepth 14000
set_option maxHeartbeats 0

theorem zeroOddRadiusSquare : Vacuum.zeroCertificate (conservationProgram false).2.1.1 := by
  have syntax_eq : (conservationProgram false).2.1.1 = f2705 := by with_unfolding_all rfl
  rw [syntax_eq]
  exact ⟨p2705, h2705, by decide +kernel⟩
#print axioms zeroOddRadiusSquare

end SchwarzschildEinstein.PureOdd.Master
